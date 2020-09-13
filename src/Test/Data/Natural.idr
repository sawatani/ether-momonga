module Test.Data.Natural

import Data.Bits
import Data.Natural
import Test.Unit.Assertions
import Test.Unit.Runners

%default total
%access export

testRotateL0 : IO Bool
testRotateL0 = do
  let a = intToBits {n=8} 1
  let given = a `rotateL` 1
  assertEquals given $ intToBits 2

testRotateL1 : IO Bool
testRotateL1 = do
  let a = intToBits {n=8} 128
  let given = a `rotateL` 1
  assertEquals given $ intToBits 1

testRotateL2 : IO Bool
testRotateL2 = do
  let a = intToBits {n=8} 129
  let given = a `rotateL` 1
  assertEquals given $ intToBits 3

testTriNumbers0 : IO Bool
testTriNumbers0 = do
  let given = triNumbers 0
  assertEquals given 1

testTriNumbers1 : IO Bool
testTriNumbers1 = do
  let given = triNumbers `map` [0, 1, 2, 3, 4, 5]
  assertEquals given [1, 3, 6, 10, 15, 21]

testAll : IO ()
testAll = do
  Reporting.runTests [
    testRotateL0
  , testRotateL1
  , testRotateL2
  , testTriNumbers0
  , testTriNumbers1
  ]
  pure ()
