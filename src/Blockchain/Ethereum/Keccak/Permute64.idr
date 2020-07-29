module Blockchain.Ethereum.Keccak.Permute64

import Data.Bits
import Data.IOArray
import Data.Matrix
import Data.Matrix.Numeric
import Data.Natural
import Data.Vect
import Data.Primitives.Views

%default total
%access export

Elem : Type
Elem = Bits 64

rounds : Nat
rounds = 12 + 2 * 6

indexesInXY : List (Nat, Nat)
indexesInXY = do
  x <- [0..4]
  y <- [0..4]
  pure (x, y)

namespace theta
  indexes : Vect 5 Int
  indexes = fromList [0..4]

  xorColumn : IOArray Elem -> Int -> IO Elem
  xorColumn array x = do
    ys <- traverse (\y => unsafeReadArray array $ 5 * y + x) indexes
    pure $ foldr1 xor ys

  xors : IOArray Elem -> IO (Vect 5 Elem)
  xors array = traverse (xorColumn array) indexes

  stepTHETA : IOArray Elem -> IO ()
  stepTHETA array = do
      leftColumn <- xors array
      let rightColumn = map (`rotateL` 1) leftColumn
      foldlM (\_, i => do
        e <- unsafeReadArray array i
        let x = cast i
        let leftX = restrict 4 (x + 4) `index` leftColumn
        let rightX = restrict 4 (x + 1) `index` rightColumn
        let e' = (e `xor` leftX) `xor` rightX
        unsafeWriteArray array i e'
      ) () [0..24]

namespace rho
  baseMatrix : Matrix 2 2 Integer
  baseMatrix = insertRow 0 [0, 1] $ row [2, 3]

  powerBase : (t : Nat) -> Matrix 2 2 Integer
  powerBase Z = Id
  powerBase (S k) = powerBase k <> baseMatrix

  calcIndex : (t : Nat) -> Int
  calcIndex t =
    let vs = getCol 0 $ powerBase t in
    let xy = map (toIntNat . finToNat . restrict 4) vs in
    5 * (index 1 xy) + (index 0 xy)

  zipPair : (k : Nat) -> (Int, Nat)
  zipPair Z = (0, Z)
  zipPair (S t) = (calcIndex t, rotation)
    where
      rotation : Nat
      rotation = (finToNat . restrict 63) $ triNumbers $ cast t

  rotations : List (Int, Nat)
  rotations = map zipPair [0..24]

  stepRHO : IOArray Elem -> IO ()
  stepRHO array = foldlM (\_, (i, s) => do
      e <- unsafeReadArray array i
      let e' = e `rotateL` s
      unsafeWriteArray array i e'
    ) () rotations

namespace pi
  calcNext : Nat -> Nat
  calcNext a =
    let x = modNatNZ a 5 SIsNotZ in
    let y = divNatNZ a 5 SIsNotZ in
    5 * x + (modNatNZ (x + 3 * y) 5 SIsNotZ)

  pairs : Stream Nat
  pairs = Stream.iterate calcNext 1

  replacingIndexes : List Int
  replacingIndexes = take 24 $ map toIntNat pairs

  stepPI : IOArray Elem -> IO ()
  stepPI array = replace replacingIndexes
    where
      replace : List Int -> IO ()
      replace [] = pure ()
      replace (firstIndex :: xs) = do
        firstElem <- unsafeReadArray array firstIndex
        lastIndex <- foldlM (\prevIndex, index => do
          e <- unsafeReadArray array index
          unsafeWriteArray array prevIndex e
          pure index
        ) firstIndex xs
        unsafeWriteArray array lastIndex firstElem
