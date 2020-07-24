module Blockchain.Ethereum.Keccak.SpongeState

import Data.Bits
import Data.IOArray
import Data.Vect
import Data.Natural
import Blockchain.Ethereum.Keccak.SpongeParam

%default total
%access export

||| Holder of bits of sponge state
||| This is a mutable and not thread-safe data
record SpongeState e where
  constructor MkSpongeState
  array : IOArray e

%name SpongeState state, state1, state2

SizeOfElem : Nat
SizeOfElem = 5 * 5

Elem : Type
Elem = Bits ElmBits

spongeState1600 : IO (SpongeState Elem)
spongeState1600 = do
  let defaultElem = MkBits $ natToBits {n = nextBytes ElmBits} 0
  array <- newArray (fromNat SizeOfElem) defaultElem
  pure $ MkSpongeState array

write :
  (state : SpongeState Elem) ->
  Vect n Elem ->
  {auto lteElms : LTE n SizeOfElem} ->
  IO ()
write state xs = xorElem 0 xs
  where
    xorElem : (i : Int) -> Vect j Elem -> IO ()
    xorElem i [] = pure ()
    xorElem i (x :: xs) = do
      y <- unsafeReadArray (array state) i
      unsafeWriteArray (array state) i (x `xor` y)
      xorElem (i + 1) xs

read :
  (state : SpongeState Elem) ->
  (n : Nat) ->
  {auto lteElms : LTE n SizeOfElem} ->
  IO (Vect n Elem)
read state n = pick n
  where
    pick : (j : Nat) -> IO $ Vect j Elem
    pick Z = pure []
    pick m@(S k) = do
      let i = toIntNat n - toIntNat m
      e <- unsafeReadArray (array state) i
      sucs <- pick k
      pure $ e :: sucs

private
rounds : Nat
rounds = 12 + 2 * LogBits

-- permute : (state : SpongeState totalBits) -> IO ()

private
theta : IOArray Elem -> IO ()
theta array = do
    leftColumn <- xors
    let rightColumn = rotateL 1 `map` leftColumn
    for [0..24] (\i => do
      e <- unsafeReadArray array i
      let x = cast i
      let leftX = restrict 4 (x + 4) `index` leftColumn
      let rightX = restrict 4 (x + 1) `index` rightColumn
      let e' = (e `xor` leftX) `xor` rightX
      unsafeWriteArray array i e'
    )
    pure ()
  where
    indexes : Vect 5 Int
    indexes = [0, 1, 2, 3, 4]
    xorColumn : Int -> IO Elem
    xorColumn x = do
      ys <- traverse (\y => unsafeReadArray array $ 5 * y + x) indexes
      pure $ foldr1 xor ys
    xors : IO (Vect 5 Elem)
    xors = traverse xorColumn indexes
