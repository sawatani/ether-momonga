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

testKeccakEmpty256 : IO Bool
testKeccakEmpty256 = do
  hash <- keccak256 []
  let given = toHex hash
  assertEquals given "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

testKeccakEmpty384 : IO Bool
testKeccakEmpty384 = do
  hash <- keccak384 []
  let given = toHex hash
  assertEquals given "2c23146a63a29acf99e73b88f8c24eaa7dc60aa771780ccc006afbfa8fe2479b2dd2b21362337441ac12b515911957ff"

testKeccakEmpty512 : IO Bool
testKeccakEmpty512 = do
  hash <- keccak512 []
  let given = toHex hash
  assertEquals given "0eab42de4c3ceb9235fc91acffe746b29c29a8c366b7c60e4e67c466f36a4304c00fa9caf9d87976ba469bcbe06713b435f091ef2769fb160cdab33d3670680e"

testSha3Empty256 : IO Bool
testSha3Empty256 = do
  hash <- sha3256 []
  let given = toHex hash
  assertEquals given "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"

testSha3Empty384 : IO Bool
testSha3Empty384 = do
  hash <- sha3384 []
  let given = toHex hash
  assertEquals given "0c63a75b845e4f7d01107d852e4c2485c51a50aaaa94fc61995e71bbee983a2ac3713831264adb47fb6bd1e058d5f004"

testSha3Empty512 : IO Bool
testSha3Empty512 = do
  hash <- sha3512 []
  let given = toHex hash
  assertEquals given "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a615b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26"

testAll : IO ()
testAll = do
  Reporting.runTests [
    testKeccakEmpty256
  , testKeccakEmpty384
  , testKeccakEmpty512
  , testSha3Empty256
  , testSha3Empty384
  , testSha3Empty512
  ]
  pure ()
