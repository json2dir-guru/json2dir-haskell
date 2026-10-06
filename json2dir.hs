-- json2dir: create the directory tree a JSON document describes, in the current directory.
-- Implements RFC J2D-1 (https://github.com/kitsunoff/awesome-json2dir/blob/main/spec/rfc-json2dir.md).
-- Uses only libraries that ship with GHC: base, bytestring, containers, unix.
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Exception (IOException, catch, finally, throwIO, try)
import Control.Monad (forM_, unless, when)
import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import qualified Data.ByteString.Unsafe as BU
import qualified Data.Map.Strict as M
import Data.Word (Word8)
import Foreign.Ptr (castPtr)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitWith)
import System.IO (stderr)
import System.IO.Error (isDoesNotExistError)
import System.Posix.ByteString (RawFilePath)
import System.Posix.Directory.ByteString (createDirectory)
import System.Posix.Files.ByteString
import System.Posix.IO.ByteString
import System.Posix.Types (Fd)

-- The validated tree. Names and contents are raw UTF-8 bytes.
data Node = File B.ByteString | Script B.ByteString | Link B.ByteString | Dir (M.Map B.ByteString Node)

-- Parsed JSON. Numbers, booleans and null are kept only to be rejected later.
data J = JStr B.ByteString | JArr [J] | JObj [(B.ByteString, J)] | JOther String

-- §3: strict UTF-8 (no overlongs, no surrogates, nothing above U+10FFFF).
validUtf8 :: B.ByteString -> Bool
validUtf8 s = go 0
  where
    n = B.length s
    at i = BU.unsafeIndex s i
    cont i = i < n && at i .&. 0xC0 == 0x80
    rng i lo hi = i < n && at i >= lo && at i <= hi
    go i
      | i >= n = True
      | b < 0x80 = go (i + 1)
      | b >= 0xC2 && b <= 0xDF = cont (i + 1) && go (i + 2)
      | b == 0xE0 = rng (i + 1) 0xA0 0xBF && cont (i + 2) && go (i + 3)
      | b == 0xED = rng (i + 1) 0x80 0x9F && cont (i + 2) && go (i + 3)
      | b >= 0xE1 && b <= 0xEF = cont (i + 1) && cont (i + 2) && go (i + 3)
      | b == 0xF0 = rng (i + 1) 0x90 0xBF && cont (i + 2) && cont (i + 3) && go (i + 4)
      | b >= 0xF1 && b <= 0xF3 = cont (i + 1) && cont (i + 2) && cont (i + 3) && go (i + 4)
      | b == 0xF4 = rng (i + 1) 0x80 0x8F && cont (i + 2) && cont (i + 3) && go (i + 4)
      | otherwise = False
      where
        b = at i

-- §3: a strict RFC 8259 parser over the input bytes.
parseDoc :: B.ByteString -> Either String J
parseDoc s = do
  (v, i) <- value (ws 0)
  if ws i == n then Right v else Left ("trailing data at byte " ++ show (ws i))
  where
    n = B.length s
    at i = if i < n then BU.unsafeIndex s i else 0
    isDigit c = c >= 0x30 && c <= 0x39
    ws i
      | i < n, at i `elem` [0x20, 0x0A, 0x0D, 0x09] = ws (i + 1)
      | otherwise = i
    bad i = Left ("invalid JSON at byte " ++ show i)

    value i = case at i of
      0x7B -> let j = ws (i + 1) in if at j == 0x7D then Right (JObj [], j + 1) else members j []
      0x5B -> let j = ws (i + 1) in if at j == 0x5D then Right (JArr [], j + 1) else elements j []
      0x22 -> do (x, j) <- str (i + 1); Right (JStr x, j)
      0x74 -> lit "true" i
      0x66 -> lit "false" i
      0x6E -> lit "null" i
      c | c == 0x2D || isDigit c -> number i
      _ -> bad i

    lit w i
      | w `B.isPrefixOf` B.drop i s = Right (JOther (BC.unpack w), i + B.length w)
      | otherwise = bad i

    members i acc = do
      when (at i /= 0x22) $ bad i
      (k, j) <- str (i + 1)
      let j' = ws j
      when (at j' /= 0x3A) $ bad j'
      (v, l) <- value (ws (j' + 1))
      let l' = ws l
          acc' = (k, v) : acc
      case at l' of
        0x2C -> members (ws (l' + 1)) acc'
        0x7D -> Right (JObj (reverse acc'), l' + 1)
        _ -> bad l'

    elements i acc = do
      (v, l) <- value i
      let l' = ws l
          acc' = v : acc
      case at l' of
        0x2C -> elements (ws (l' + 1)) acc'
        0x5D -> Right (JArr (reverse acc'), l' + 1)
        _ -> bad l'

    digits i = if isDigit (at i) then digits (i + 1) else i
    number i = do
      let j0 = if at i == 0x2D then i + 1 else i
      j1 <-
        if at j0 == 0x30
          then Right (j0 + 1)
          else if isDigit (at j0) then Right (digits j0) else bad j0
      j2 <-
        if at j1 == 0x2E
          then if isDigit (at (j1 + 1)) then Right (digits (j1 + 1)) else bad (j1 + 1)
          else Right j1
      j3 <-
        if at j2 == 0x65 || at j2 == 0x45
          then do
            let k = if at (j2 + 1) == 0x2B || at (j2 + 1) == 0x2D then j2 + 2 else j2 + 1
            if isDigit (at k) then Right (digits k) else bad k
          else Right j2
      Right (JOther "number", j3)

    -- A string body starting after the opening quote; returns its UTF-8 bytes.
    str i0 = go i0 []
      where
        plain c = c >= 0x20 && c /= 0x22 && c /= 0x5C
        go j acc =
          let k = j + B.length (B.takeWhile plain (B.drop j s))
              acc' = B.take (k - j) (B.drop j s) : acc
           in if k >= n
                then Left "unterminated string"
                else case at k of
                  0x22 -> Right (B.concat (reverse acc'), k + 1)
                  0x5C -> do (bytes, k') <- escape (k + 1); go k' (bytes : acc')
                  _ -> Left ("control character in string at byte " ++ show k)
        escape k = case at k of
          0x22 -> one 0x22
          0x5C -> one 0x5C
          0x2F -> one 0x2F
          0x62 -> one 0x08
          0x66 -> one 0x0C
          0x6E -> one 0x0A
          0x72 -> one 0x0D
          0x74 -> one 0x09
          0x75 -> do
            hi <- hex4 (k + 1)
            if hi >= 0xD800 && hi <= 0xDBFF
              then do
                when (at (k + 5) /= 0x5C || at (k + 6) /= 0x75) $ Left "unpaired surrogate in string"
                lo <- hex4 (k + 7)
                unless (lo >= 0xDC00 && lo <= 0xDFFF) $ Left "unpaired surrogate in string"
                Right (utf8 (0x10000 + ((hi - 0xD800) `shiftL` 10) + (lo - 0xDC00)), k + 11)
              else
                if hi >= 0xDC00 && hi <= 0xDFFF
                  then Left "unpaired surrogate in string"
                  else Right (utf8 hi, k + 5)
          _ -> bad k
          where
            one c = Right (B.singleton c, k + 1)
        hex4 k = foldl step (Right 0) [k .. k + 3]
          where
            step acc i = do
              a <- acc
              d <- hexDigit (at i) i
              Right (a * 16 + d)
        hexDigit c i
          | isDigit c = Right (fromIntegral c - 0x30)
          | c >= 0x61 && c <= 0x66 = Right (fromIntegral c - 0x57)
          | c >= 0x41 && c <= 0x46 = Right (fromIntegral c - 0x37)
          | otherwise = bad i

utf8 :: Int -> B.ByteString
utf8 c
  | c < 0x80 = B.pack [w c]
  | c < 0x800 = B.pack [w (0xC0 .|. shiftR c 6), cb c]
  | c < 0x10000 = B.pack [w (0xE0 .|. shiftR c 12), cb (shiftR c 6), cb c]
  | otherwise = B.pack [w (0xF0 .|. shiftR c 18), cb (shiftR c 12), cb (shiftR c 6), cb c]
  where
    w :: Int -> Word8
    w = fromIntegral
    cb x = w (0x80 .|. (x .&. 0x3F))

-- §4, §6: validate the whole document before touching the file system.
-- Duplicate names: the last occurrence wins (M.fromList keeps the last).
toNode :: B.ByteString -> J -> Either String Node
toNode _ (JStr c) = Right (File c)
toNode w (JArr [JStr "link", JStr t])
  | 0 `B.elem` t = Left (BC.unpack w ++ ": a link target cannot contain NUL")
  | otherwise = Right (Link t)
toNode _ (JArr [JStr "script", JStr c]) = Right (Script c)
toNode w (JArr _) = Left (BC.unpack w ++ ": an array must be [\"link\", target] or [\"script\", content]")
toNode w (JObj ms) = Dir . M.fromList <$> mapM member ms
  where
    member (k, v) = do
      let p = if w == "." then k else w <> "/" <> k
      when (B.null k || k == "." || k == ".." || 0x2F `B.elem` k || 0 `B.elem` k) $
        Left (BC.unpack p ++ ": invalid name")
      node <- toNode p v
      Right (k, node)
toNode w (JOther t) = Left (BC.unpack w ++ ": " ++ t ++ " values are not allowed")

lstatMaybe :: RawFilePath -> IO (Maybe FileStatus)
lstatMaybe p = (Just <$> getSymbolicLinkStatus p) `catch` \e ->
  if isDoesNotExistError e then pure Nothing else throwIO e

-- O_CREAT|O_EXCL|O_NOFOLLOW: never writes through an entry that appeared after removal.
writeFileAt :: RawFilePath -> B.ByteString -> Bool -> IO ()
writeFileAt p c executable = do
  fd <- openFd p WriteOnly defaultFileFlags {exclusive = True, nofollow = True, creat = Just 0o666}
  body fd `finally` closeFd fd
  where
    body fd = do
      writeAll fd c
      when executable $ do
        st <- getFdStatus fd
        setFdMode fd ((fileMode st .&. 0o7777) .|. 0o111)

writeAll :: Fd -> B.ByteString -> IO ()
writeAll fd c = unless (B.null c) $ do
  k <- BU.unsafeUseAsCStringLen c $ \(ptr, len) -> fdWriteBuf fd (castPtr ptr) (fromIntegral len)
  writeAll fd (B.drop (fromIntegral k) c)

-- §5: directories are reused; anything else (never followed) is removed and recreated.
apply :: RawFilePath -> M.Map B.ByteString Node -> IO ()
apply dir tree = forM_ (M.toAscList tree) $ \(name, node) -> do
  let p = if dir == "." then name else dir <> "/" <> name
  existing <- lstatMaybe p
  case node of
    Dir sub -> do
      case existing of
        Just st | isDirectory st -> pure ()
        Just _ -> removeLink p >> createDirectory p 0o777
        Nothing -> createDirectory p 0o777
      apply p sub
    _ -> do
      case existing of
        Just st
          | isDirectory st -> ioError (userError (BC.unpack p ++ ": a directory is in the way"))
          | otherwise -> removeLink p
        Nothing -> pure ()
      case node of
        File c -> writeFileAt p c False
        Script c -> writeFileAt p c True
        Link t -> createSymbolicLink t p

die' :: String -> IO a
die' msg = do
  -- Messages carry raw name bytes as Chars 0..255; BC.pack restores those bytes.
  B.hPut stderr (BC.pack ("json2dir: " ++ msg ++ "\n"))
  exitWith (ExitFailure 1)

main :: IO ()
main = do
  args <- getArgs
  unless (null args) $ do
    B.hPut stderr "usage: json2dir < document.json\n"
    exitWith (ExitFailure 2)
  input <- B.getContents
  unless (validUtf8 input) $ die' "input is not valid UTF-8"
  let body = if "\xEF\xBB\xBF" `B.isPrefixOf` input then B.drop 3 input else input
  doc <- either (die' . ("input is not valid JSON: " ++)) pure (parseDoc body)
  tree <- case doc of
    JObj _ -> either die' pure (toNode "." doc)
    _ -> die' "the root of the document must be an object"
  r <- try (case tree of Dir m -> apply "." m; _ -> pure ())
  case r of
    Left e -> die' (show (e :: IOException))
    Right () -> pure ()
