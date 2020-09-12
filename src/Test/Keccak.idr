module Test.Keccak

import Data.Bits
import Data.Bytes
import Data.Crypt.Keccak
import Data.Crypt.Keccak.SpongeParam
import Data.IOArray
import Data.Iterable
import Data.Vect
import Test.Unit.Assertions
import Test.Unit.Runners

%default total
%access export

testEmpty256 : IO Bool
testEmpty256 = do
  hash <- keccak256 []
  let given = toHex hash
  assertEquals given "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

testEmpty384 : IO Bool
testEmpty384 = do
  hash <- keccak384 []
  let given = toHex hash
  assertEquals given "2c23146a63a29acf99e73b88f8c24eaa7dc60aa771780ccc006afbfa8fe2479b2dd2b21362337441ac12b515911957ff"

testEmpty512 : IO Bool
testEmpty512 = do
  hash <- keccak512 []
  let given = toHex hash
  assertEquals given "0eab42de4c3ceb9235fc91acffe746b29c29a8c366b7c60e4e67c466f36a4304c00fa9caf9d87976ba469bcbe06713b435f091ef2769fb160cdab33d3670680e"

testAll : IO ()
testAll = do
  Reporting.runTests [
    testEmpty256
  ]
  pure ()
