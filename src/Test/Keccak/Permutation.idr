module Test.Keccak.Permutation

import Data.Bits
import Data.Crypt.Keccak.Permute64
import Data.Crypt.Keccak.SpongeParam
import Data.IOArray
import Data.List
import Data.Matrix
import Data.Matrix.Numeric
import Data.Vect
import Test.Unit.Assertions
import Test.Unit.Runners

%default total
%access export

zeroElm : Elem
zeroElm = intToBits 0

mkArray : Int -> IO (IOArray Elem)
mkArray n = newArray n zeroElm

toListArray : IOArray Elem -> Nat -> IO (List Nat)
toListArray x n = reverse <$> reversedList x n
  where
    reversedList : IOArray Elem -> Nat -> IO (List Nat)
    reversedList x Z = pure []
    reversedList x (S k) = do
      v <- unsafeReadArray x (fromNat k)
      more <- reversedList x k
      pure $ (fromInteger $ bitsToInt v) :: more

namespace theta
  testIndexes : IO Bool
  testIndexes = do
    let given = theta.indexes
    assertEquals given [0, 1, 2, 3, 4]

  testXorColumn0 : IO Bool
  testXorColumn0 = do
    array <- mkArray 25
    given <- theta.xorColumn array 0
    assertEquals given zeroElm

  testXorColumn1 : IO Bool
  testXorColumn1 = do
    array <- mkArray 25
    unsafeWriteArray array 0 $ intToBits 1
    unsafeWriteArray array 5 $ intToBits 2
    unsafeWriteArray array 10 $ intToBits 4
    unsafeWriteArray array 15 $ intToBits 8
    unsafeWriteArray array 20 $ intToBits 16
    given <- theta.xorColumn array 0
    assertEquals given $ intToBits 31

  testXorColumn2 : IO Bool
  testXorColumn2 = do
    array <- mkArray 25
    unsafeWriteArray array 1 $ intToBits 1
    unsafeWriteArray array 6 $ intToBits 2
    unsafeWriteArray array 11 $ intToBits 8
    unsafeWriteArray array 16 $ intToBits 8
    unsafeWriteArray array 21 $ intToBits 16
    given <- theta.xorColumn array 1
    assertEquals given $ intToBits 19

namespace rho
  testBaseMatrix : IO Bool
  testBaseMatrix = do
    let given = baseMatrix
    assertEquals (getRow 0 given) [0, 1]
    assertEquals (getRow 1 given) [2, 3]
    assertEquals (getCol 0 given) [0, 2]
    assertEquals (getCol 1 given) [1, 3]

  testPowerBase0 : IO Bool
  testPowerBase0 = do
    assertEquals (powerBase 0) Id

  testPowerBase1 : IO Bool
  testPowerBase1 = do
    assertEquals (powerBase 1) baseMatrix

  testRotations : IO Bool
  testRotations = do
    let ns = sort rotations
    let given = map snd ns
    assertEquals given [  0, 36,  3, 41, 18
                       ,  1, 44, 10, 45,  2
                       , 62,  6, 43, 15, 61
                       , 28, 55, 25, 21, 56
                       , 27, 20, 39,  8, 14 ]

namespace pi
  genIndexPairs : (n : Nat) -> Vect n (Nat, Nat)
  genIndexPairs Z = []
  genIndexPairs (S k) = (k, calcNext k) :: genIndexPairs k

  indexList : Vect n a -> Vect n (Nat, a)
  indexList {n = Z} _ = []
  indexList {n = (S k)} (x :: xs) = (k, x) :: indexList xs

  testIndexes : IO Bool
  testIndexes = do
    let given = genIndexPairs 25
    assertEquals given $ indexList $ reverse [ 0, 15, 5, 20, 10
                                             , 6, 21, 11, 1, 16
                                             , 12, 2, 17, 7, 22
                                             , 18, 8, 23, 13, 3
                                             , 24, 14, 4, 19, 9 ]

  placeIndex : IOArray Elem -> Nat -> IO ()
  placeIndex x Z = pure ()
  placeIndex x (S k) = do
    unsafeWriteArray x (fromNat k) (intToBits $ fromNat k)
    placeIndex x k

  testReplace : IO Bool
  testReplace = do
    array <- mkArray 25
    placeIndex array 25
    stepPI array
    given <- toListArray array 25
    assertEquals given [ 0, 15, 5, 20, 10
                       , 6, 21, 11, 1, 16
                       , 12, 2, 17, 7, 22
                       , 18, 8, 23, 13, 3
                       , 24, 14, 4, 19, 9 ]

namespace chi
  testXorColumns : IO Bool
  testXorColumns= do
    array <- mkArray 25
    -- column 0
    unsafeWriteArray array  0 $ intToBits 1
    unsafeWriteArray array  5 $ intToBits 1
    unsafeWriteArray array 10 $ intToBits 1
    unsafeWriteArray array 15 $ intToBits 1
    unsafeWriteArray array 20 $ intToBits 1
    -- column 1
    unsafeWriteArray array  1 $ intToBits 1
    unsafeWriteArray array  6 $ intToBits 2
    unsafeWriteArray array 11 $ intToBits 3
    unsafeWriteArray array 16 $ intToBits 4
    unsafeWriteArray array 21 $ intToBits 5
    stepCHI array
    given <- toListArray array 25
    assertEquals given [ 1,  0,  0,  0,  0
                       , 1,  6,  0,  0,  0
                       , 1,  2,  0,  0,  0
                       , 1,  4,  0,  0,  0
                       , 1,  7,  0,  0,  0 ]

namespace iota
  constants : List Integer
  constants = [ 0x0000000000000001, 0x0000000000008082, 0x800000000000808A
              , 0x8000000080008000, 0x000000000000808B, 0x0000000080000001
              , 0x8000000080008081, 0x8000000000008009, 0x000000000000008A
              , 0x0000000000000088, 0x0000000080008009, 0x000000008000000A
              , 0x000000008000808B, 0x800000000000008B, 0x8000000000008089
              , 0x8000000000008003, 0x8000000000008002, 0x8000000000000080
              , 0x000000000000800A, 0x800000008000000A, 0x8000000080008081
              , 0x8000000000008080, 0x0000000080000001, 0x8000000080008008 ]

  testRoundValues : IO Bool
  testRoundValues = do
    let given = toList $ bitsToInt `map` iota.roundValues
    assertEquals given constants

testAll : IO ()
testAll = do
  Reporting.runTests [
    theta.testIndexes
  , theta.testXorColumn0
  , theta.testXorColumn1
  , theta.testXorColumn2
  , rho.testBaseMatrix
  , rho.testPowerBase0
  , rho.testPowerBase1
  , rho.testRotations
  , pi.testIndexes
  , pi.testReplace
  , chi.testXorColumns
  , iota.testRoundValues
  ]
  pure ()
