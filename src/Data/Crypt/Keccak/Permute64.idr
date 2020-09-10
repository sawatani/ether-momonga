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

ROUNDS : Nat
ROUNDS = 12 + 2 * LogBits

WORDS_MAX : Nat
WORDS_MAX = 5 * 5 -1

namespace theta
  indexes : Vect 5 Int
  indexes = fromList $ toIntNat `map` natRange 5

  xorColumn : IOArray Elem -> Int -> IO Elem
  xorColumn array j = do
    columns <- traverse (\i => unsafeReadArray array $ 5 * i + j) indexes
    pure $ foldr1 xor columns

  xors : IOArray Elem -> IO (Vect 5 Elem)
  xors array = traverse (xorColumn array) indexes

  stepTHETA : IOArray Elem -> IO ()
  stepTHETA array = do
      leftColumn <- xors array
      let rightColumn = map (`rotateL` 1) leftColumn
      foldlM (\_, pos => do
        e <- unsafeReadArray array pos
        let i = cast pos
        let leftI = restrict 4 (i + 4) `index` leftColumn
        let rightI = restrict 4 (i + 1) `index` rightColumn
        let e' = (e `xor` leftI) `xor` rightI
        unsafeWriteArray array pos e'
      ) () $ toIntNat `map` natRange (S WORDS_MAX)

namespace rho
  baseMatrix : Matrix 2 2 Integer
  baseMatrix = insertRow 0 [0, 1] $ row [2, 3]

  powerBase : (t : Nat) -> Matrix 2 2 Integer
  powerBase Z = Id
  powerBase (S k) = powerBase k <> baseMatrix

  calcIndex : (t : Nat) -> Int
  calcIndex t =
    let vs = getCol 0 $ powerBase t in
    let ij = map (toIntNat . finToNat . restrict 4) vs in
    5 * (index 1 ij) + (index 0 ij)

  zipPair : (k : Nat) -> (Int, Nat)
  zipPair Z = (0, Z)
  zipPair (S t) = (calcIndex t, rotation)
    where
      rotation : Nat
      rotation = (finToNat . restrict 63) $ triNumbers $ cast t

  rotations : List (Int, Nat)
  rotations = map zipPair $ natRange (S WORDS_MAX)

  stepRHO : IOArray Elem -> IO ()
  stepRHO array = foldlM (\_, (i, s) => do
      e <- unsafeReadArray array i
      let e' = e `rotateL` s
      unsafeWriteArray array i e'
    ) () rotations

namespace pi
  calcNext : Nat -> Nat
  calcNext a =
    let y = divNatNZ a 5 SIsNotZ in
    let x = modNatNZ a 5 SIsNotZ in
    let x' = modNatNZ (3 * y + x) 5 SIsNotZ in
    let y' = x in
    5 * y' + x'

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
  calcPos : (x : Nat) -> (y : Nat) -> Int
  calcPos x y =
    let y' = modNatNZ y 5 SIsNotZ in
    let x' = modNatNZ x 5 SIsNotZ in
    toIntNat $ 5 * y' + x'

  data Cache : Type where
    NoCache : Cache
    MkCache : Elem -> Cache

  readAt : IOArray Elem -> (y : Nat) ->
    Cache -> (x : Nat) -> IO Elem
  readAt array y NoCache x = unsafeReadArray array $ calcPos x y
  readAt _ _ (MkCache e) _ = pure e

  eachColumn : IOArray Elem -> (y : Nat) ->
    (Cache, Cache) -> (x : Nat) ->
    IO (Cache, Cache)
  eachColumn array y (p1, p2) x =
    let at = readAt array y in
    let pos = calcPos x y in
    do
      e0 <- unsafeReadArray array pos
      e1 <- p1 `at` (x + 1)
      e2 <- p2 `at` (x + 2)
      let e = e0 `xor` (complement e1 `and` e2)
      unsafeWriteArray array pos e
      pure (MkCache e0, MkCache e1)

  stepCHI : IOArray Elem -> IO ()
  stepCHI array = foldlM (\_, y => do
    foldlM (eachColumn array y) (NoCache, NoCache) [4..0]
    pure ()
  ) () [4..0]

namespace iota
  LFSRState : Type
  LFSRState = Bits 8

  one : Elem
  one = intToBits 1

  eachRound : Elem -> (state : LFSRState) ->
    (m : Nat) -> {auto lte : LTE m (S LogBits)} -> (LFSRState, Elem)
  eachRound bits state Z = (state, bits)
  eachRound bits state (S k) {lte} =
    let nextBits = if output state
      then
        let lteBoth = fromLteSucc lte in
        let j = intToBits $ fromNat $ LogBits - k in
        let pos = shiftLeft one j `minus` one in
        bits `xor` shiftLeft one pos
      else bits in
    let lteL = lteSuccLeft lte in
    eachRound nextBits (next state) k

  mkValues : (state : LFSRState) -> (n : Nat) -> Vect n Elem
  mkValues _ Z = []
  mkValues state (S k) =
    let (next, bits) = eachRound (intToBits 0) state (S LogBits) {lte=lteRefl} in
    bits :: mkValues next k

  roundValues : Vect ROUNDS Elem
  roundValues = mkValues value1 ROUNDS

  stepIOTA : IOArray Elem -> (roundIndex : Fin ROUNDS) -> IO ()
  stepIOTA array roundIndex = do
    v <- unsafeReadArray array 0
    unsafeWriteArray array 0 $ v `xor` index roundIndex roundValues

roundAll : IOArray Elem -> IO ()
roundAll array = foldlM (\_, i => do
  stepTHETA array
  stepRHO array
  stepPI array
  stepCHI array
  stepIOTA array $ restrict (ROUNDS - 1) $ fromNat i
) () $ natRange ROUNDS
