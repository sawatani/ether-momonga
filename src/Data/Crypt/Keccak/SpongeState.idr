module Data.Crypt.Keccak.SpongeState

import Data.Bits
import Data.IOArray
import Data.Vect
import Data.Natural
import Data.Crypt.Keccak.SpongeParam
import Data.Crypt.Keccak.Permute64

%default total
%access export

||| Holder of bits of sponge state
||| This is a mutable and not thread-safe data
public export
record SpongeState e where
  constructor MkSpongeState
  param : SpongeParam
  array : IOArray e

spongeState1600 : SpongeParam {totalBits = 1600} -> IO (SpongeState Elem)
spongeState1600 param = do
  array <- newArray (fromNat $ totalElms param) $ intToBits 0
  pure $ MkSpongeState param array

write :
  (state : SpongeState Elem) ->
  Vect n Elem ->
  {auto lteElms : LTE n (totalElms $ param state)} ->
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
  {auto lteElms : LTE n (totalElms $ param state)} ->
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

permute : (state : SpongeState Elem) -> IO ()
permute state = roundAll $ array state
