module Test.Keccak.Padding

import Data.Bits
import Data.Crypt.Keccak.Padding
import Data.Crypt.Keccak.SpongeParam
import Data.Iterable
import Data.Vect
import Test.Unit.Assertions
import Test.Unit.Runners

%default total
%access export

mkSrc : List Integer -> LazyList (Bits 8)
mkSrc xs = fromList $ intToBits `map` xs

testPad0 : IO Bool
testPad0 = do
  let given = toList $ pad {n=4} keccakPad SIsNotZ []
  let bits = intToBits `map` [1, 0, 0, 0x8000000000000000]
  assertEquals given [bits]

testPad1 : IO Bool
testPad1 = do
  let given = toList $ pad {n=4} keccakPad SIsNotZ $ mkSrc [7]
  let bits = intToBits `map` [0x107, 0, 0, 0x8000000000000000]
  assertEquals given [bits]

testPad2 : IO Bool
testPad2 = do
  let given = toList $ pad {n=4} keccakPad SIsNotZ $ mkSrc [7, 0]
  let bits = intToBits `map` [0x10007, 0, 0, 0x8000000000000000]
  assertEquals given [bits]

testPad3 : IO Bool
testPad3 = do
  let given = toList $ pad {n=4} keccakPad SIsNotZ $ mkSrc [7, 8, 9, 10, 11, 12, 13]
  let bits = intToBits `map` [0x010d0c0b0a090807, 0, 0, 0x8000000000000000]
  assertEquals given [bits]

testPad4 : IO Bool
testPad4 = do
  let given = toList $ pad {n=4} keccakPad SIsNotZ $ mkSrc [7, 8, 9, 10, 11, 12, 13, 14]
  let bits = intToBits `map` [0x0e0d0c0b0a090807, 1, 0, 0x8000000000000000]
  assertEquals given [bits]

testPad5 : IO Bool
testPad5 = do
  let given = toList $ pad {n=4} keccakPad SIsNotZ $ mkSrc $ fromNat `map` natRange (8 * 4)
  let bits0 = intToBits `map` [
    0x0706050403020100
  , 0x0f0e0d0c0b0a0908
  , 0x1716151413121110
  , 0x1f1e1d1c1b1a1918
  ]
  let bits1 = intToBits `map` [1, 0, 0, 0x8000000000000000]
  assertEquals given $ bits0 :: bits1 :: []

testAll : IO ()
testAll = do
  Reporting.runTests [
    testPad0
  , testPad1
  , testPad2
  , testPad3
  , testPad4
  , testPad5
  ]
  pure ()
