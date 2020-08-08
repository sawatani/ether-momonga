module Data.Crypt.Keccak.Permute64

import Data.Bits
import Data.IOArray
import Data.Matrix
import Data.Matrix.Numeric
import Data.Natural
import Data.Vect
import Data.Primitives.Views
import Data.Crypt.LFSR
import Data.Crypt.Keccak.SpongeParam

%default total
%access export

Elem : Type
Elem = Bits ElmBits

ROUNDS : Nat
ROUNDS = 12 + 2 * LogBits

WORDS_MAX : Nat
WORDS_MAX = 5 * 5 -1

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
      ) () [0..(toIntNat WORDS_MAX)]

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
  rotations = map zipPair [0..WORDS_MAX]

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

  indexes : List Int
  indexes = take WORDS_MAX $ map toIntNat pairs

  stepPI : IOArray Elem -> IO ()
  stepPI array = replace indexes
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

namespace chi
  calcIndex : Nat -> Nat -> Int
  calcIndex x y = toIntNat $ 5 * y + (modNatNZ x 5 SIsNotZ)

  data Cache : Type where
    NoCache : Cache
    MkCache : Elem -> Cache

  readAt : IOArray Elem -> (y : Nat) ->
    Cache -> (x : Nat) -> IO Elem
  readAt array y NoCache x = unsafeReadArray array $ calcIndex x y
  readAt _ _ (MkCache e) _ = pure e

  eachOnY : IOArray Elem -> (y : Nat) ->
    (Cache, Cache) -> (x : Nat) ->
    IO (Cache, Cache)
  eachOnY array y (p1, p2) x = let at = readAt array y in do
    let index = calcIndex x y
    e0 <- unsafeReadArray array index
    e1 <- p1 `at` (x + 1)
    e2 <- p2 `at` (x + 2)
    let e = e0 `xor` (complement e1 `and` e2)
    unsafeWriteArray array index e
    pure (MkCache e0, MkCache e1)

  stepCHI : IOArray Elem -> IO ()
  stepCHI array = foldlM (\_, y => do
    foldlM (eachOnY array y) (NoCache, NoCache) [4..0]
    pure ()
  ) () [4..0]

namespace iota
  startState : Bits 8
  startState = value1

  zero : Bits 8
  zero = intToBits 0

  eachRound : (bits : Bits 8) -> (state : Bits 8) ->
    (m : Nat) -> {auto lte : LTE m (S LogBits)} -> (Bits 8, Bits 8)
  eachRound state bits Z = (state, bits)
  eachRound state bits (S k) {lte} =
    let lteL = lteSuccLeft lte in
    let lteBoth = fromLteSucc lte in
    let j = intToBits $ fromNat $ LogBits - k in
    let pos = shiftLeft value1 j `minus` intToBits 1 in
    let nextBits = if output state then bits `xor` shiftLeft value1 pos else bits in
    eachRound (next state) nextBits k

  rounds : (state : Bits 8) -> (n : Nat) -> Vect n (Bits 8)
  rounds _ Z = []
  rounds state (S k) =
    let (next, bits) = eachRound state zero (S LogBits) {lte=lteRefl} in
    bits :: rounds next k

  constants : Vect ROUNDS (Bits 8)
  constants = rounds startState ROUNDS
