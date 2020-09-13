module Test.Data.Crypt.LFSR

import Data.Bits
import Data.Crypt.LFSR
import Data.List
import Test.Unit.Assertions
import Test.Unit.Runners

%default total
%access export

genList : (tp : Taps (S n)) -> (init : Bits (S n)) -> (count : Nat) -> List (Bits (S n))
genList _ init Z = []
genList tp init (S k) = init :: genList tp (next init) k

testTaps2 : IO Bool
testTaps2 = do
  let bits = genList taps2 value1 3
  let given = bitsToInt `map` bits
  assertEquals given [1, 2, 3]

testTaps3 : IO Bool
testTaps3 = do
  let bits = genList taps3 value1 7
  let given = bitsToInt `map` bits
  assertEquals given [1, 2, 4, 5, 7, 3, 6]

testTaps8 : IO Bool
testTaps8 = do
  let bits = genList taps8 value1 255
  let given = size $ nub bits
  assertEquals given 255

testAll : IO ()
testAll = do
  Reporting.runTests [
    testTaps2
  , testTaps3
  , testTaps8
  ]
  pure ()
