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

namespace pi
  calcNext : (Nat, Nat) -> (Int, (Nat, Nat))
  calcNext (x, y) =
    let a = 5 * y + x in
    let b = 5 * x + (modNatNZ (x + 3 * y) 5 SIsNotZ) in
    let x' = modNatNZ b 5 SIsNotZ in
    let y' = divNatNZ b 5 SIsNotZ in
    (toIntNat a, (x', y'))

  pairs : Stream (Int, (Nat, Nat))
  pairs = Stream.iterate (calcNext . snd) $ calcNext (1, 0)

  replacingIndexes : List Int
  replacingIndexes = take 24 $ map fst pairs

theta : IOArray Elem -> IO ()
theta array = do
    leftColumn <- xors
    let rightColumn = map (`rotateL` 1) leftColumn
    foldlM (\_, i => do
      e <- unsafeReadArray array i
      let x = cast i
      let leftX = restrict 4 (x + 4) `index` leftColumn
      let rightX = restrict 4 (x + 1) `index` rightColumn
      let e' = (e `xor` leftX) `xor` rightX
      unsafeWriteArray array i e'
    ) () [0..24]
  where
    indexes : Vect 5 Int
    indexes = fromList [0..4]
    xorColumn : Int -> IO Elem
    xorColumn x = do
      ys <- traverse (\y => unsafeReadArray array $ 5 * y + x) indexes
      pure $ foldr1 xor ys
    xors : IO (Vect 5 Elem)
    xors = traverse xorColumn indexes

rho : IOArray Elem -> IO ()
rho array = foldlM (\_, (i, s) => do
    e <- unsafeReadArray array i
    let e' = e `rotateL` s
    unsafeWriteArray array i e'
  ) () rotations

pi : IOArray Elem -> IO ()
pi array = replace replacingIndexes
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
