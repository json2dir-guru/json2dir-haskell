# json2dir-haskell

json2dir in Haskell: one file, only the libraries that ship with GHC (base, bytestring, containers, unix), hand-written strict JSON parser.

    ghc -O -outputdir /tmp/json2dir-hs-build -o out/json2dir json2dir.hs
    out/json2dir < document.json
