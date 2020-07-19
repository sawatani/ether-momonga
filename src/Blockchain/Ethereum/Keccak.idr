module Blockchain.Ethereum.Keccak

import Data.Natural

%default total
%access private

export
data SpongeParam : (totalBits : Nat) -> (hashBits : Nat) -> Type where
  MkSpongeParam :
    {default 1600 totalBits : Nat} ->
    (hashBits : Nat) ->
    {auto prf0 : capaticyBits = hashBits * 2} ->
    {auto prf1 : LTE capaticyBits totalBits} ->
    {auto prf2 : rateBits = totalBits - capaticyBits} ->
    {auto prf3 : LTE hashBits rateBits} ->
    SpongeParam totalBits hashBits

export
rateBits : SpongeParam totalBits hashBits -> Nat
rateBits (MkSpongeParam {totalBits} hashBits {prf0} {prf1}) =
  let p = prf in totalBits - hashBits * 2
  where
    prf : LTE (hashBits * 2) totalBits
    prf = rewrite sym prf0 in prf1

lteBy64 : (a : Nat) -> (b : Nat) -> {auto p : LTE a b}  -> LTE (a * 64) (b * 64)
lteBy64 _ _ {p} = lteCongMult 64 p

export
spongeParam256 : SpongeParam 1600 256
spongeParam256 =
  let prf1 = lteBy64 8 25 in -- 8 * 64 = 512, 25 * 64 = 1600
  let prf2 = lteBy64 4 17 in -- 4 * 64 = 256, 17 * 64 = 1088
  MkSpongeParam 256
