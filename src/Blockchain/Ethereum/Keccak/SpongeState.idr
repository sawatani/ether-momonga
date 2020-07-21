module Blockchain.Ethereum.Keccak.Sponge


import Data.Bits
import Data.IOArray
import Data.Nat
import Data.Nat.DivMod
import Data.Primitives.Views
import Data.Vect

%default total
%access private

||| Holder of bits of sponge state
export
data SpongeState : (lengthInBit : Nat) -> Type where
  MkSpongeState :
    (sizeOfElem : Nat) ->
    (array : IOArray Bits64) ->
    SpongeState (sizeOfElem * 64)

%name SpongeState state, state1, state2

mkSpongeState : (n : Nat) -> IO $ SpongeState (n * 64)
mkSpongeState n = do
  array <- newArray (cast n) $ natToBits {n=8} 0
  pure $ MkSpongeState n array

export
spongeState1600 : IO (SpongeState 1600)
spongeState1600 = mkSpongeState 25

export
write :
  SpongeState n ->
  Vect m Bits64 ->
  {auto prf : LTE (m * 64) n} ->
  IO (SpongeState n)
write state xs = pure state

doWrite : IO ()
doWrite = do
  state <- spongeState1600
  let vect = map (natToBits {n=8}) $ the (Vect _ Nat) $ fromList [1..17]
  -- write state vect
  pure $ ?answer
