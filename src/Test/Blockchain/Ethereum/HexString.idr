module Test.Blockchain.Ethereum.HexString

import Blockchain.Ethereum.HexString
import Test.Unit.Assertions
import Test.Unit.Runners

%default total
%access export

assertParsedHex : String -> Nat -> IO Bool
assertParsedHex src len = case parseHex src of
  Nothing => assertTrue False
  Just (n ** hex) => do
    assertEquals n len
    assertEquals (show hex) src

testParseHexOK : IO Bool
testParseHexOK = do
  assertParsedHex "0x" 0
  assertParsedHex "0x0123456789" 5
  assertParsedHex "0x01234567890123456789" 10
  assertParsedHex "0x01234567890123456789AB" 11
  assertParsedHex "0x0123456789ABCDEFABCDEF0123456789ABCDEFAB" 20

testParseHexNG : IO Bool
testParseHexNG = do
  assertNothing $ parseHex "0x012"
  assertNothing $ parseHex "0xABC"
  assertNothing $ parseHex "0xYZ"
  assertNothing $ parseHex "ABCD"
  assertNothing $ parseHex "0123"

testAll : IO ()
testAll = do
  Reporting.runTests [
    testParseHexOK
  , testParseHexNG
  ]
  pure ()
