module Blockchain.Ethereum.Keccak.Sponge


import Data.Bits
import Data.IOArray
import Data.Nat
import Data.Nat.DivMod
import Data.Primitives.Views
import Data.Vect

%default total
%access export

Elem : Type
Elem = Bits 64

||| Holder of bits of sponge state
data SpongeState : (lengthInBit : Nat) -> Type where
  MkSpongeState :
    (sizeOfElem : Nat) ->
    (array : IOArray Elem) ->
    SpongeState (sizeOfElem * 64)

%name SpongeState state, state1, state2

sizeOfElem : SpongeState n -> Nat
sizeOfElem (MkSpongeState sizeOfElem _) = sizeOfElem

private
ioArray : SpongeState n -> IOArray Elem
ioArray (MkSpongeState _ array) = array

private
mkSpongeState : (n : Nat) -> IO $ SpongeState (n * 64)
mkSpongeState n = do
  array <- newArray (cast n) (MkBits $ natToBits {n=8} 0)
  pure $ MkSpongeState n array

spongeState1600 : IO (SpongeState 1600)
spongeState1600 = mkSpongeState 25

private
write :
  (state : SpongeState totalBits) ->
  Vect n Elem ->
  {auto lteElms : LTE n (sizeOfElem state)} ->
  IO (SpongeState totalBits)
write state@(MkSpongeState _ array) xs =
  do
    xorElem 0 xs
    pure state
  where
    xorElem : (i : Int) -> Vect j Elem -> IO ()
    xorElem i [] = pure ()
    xorElem i (x :: xs) = do
      y <- unsafeReadArray array i
      unsafeWriteArray array i (x `xor` y)
      xorElem (i + 1) xs

private
read :
  (state : SpongeState totalBits) ->
  (n : Nat) ->
  {auto lteElms : LTE n (sizeOfElem state)} ->
  IO (Vect n Elem)
read (MkSpongeState _ array) n = pick n
  where
    pick : (j : Nat) -> IO $ Vect j Elem
    pick Z = pure []
    pick m@(S k) = do
      sucs <- pick k
      let i = toIntNat n - toIntNat m
      e <- unsafeReadArray array i
      pure $ e :: sucs
