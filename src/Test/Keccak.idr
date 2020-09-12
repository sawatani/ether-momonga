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
  hash <- keccak spongeParam256 []
  let given = toHex hash
  assertEquals given "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

testAll : IO ()
testAll = do
  Reporting.runTests [
    testEmpty256
  ]
  pure ()
