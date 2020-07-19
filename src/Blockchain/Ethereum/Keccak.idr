module Blockchain.Ethereum.Keccak

import Data.Natural

%default total
%access private

export
data SpongeParam : {default 1600 totalBits : Nat} -> (hashBits : Nat) -> Type where
  MkSpongeParam :
    {default 1600 totalBits : Nat} ->
    (hashBits : Nat) ->
    {auto prf1 : capaticyBits = hashBits * 2} ->
    {auto prf2 : LTE capaticyBits totalBits} ->
    {auto prf3 : rateBits = totalBits - capaticyBits} ->
    {auto prf4 : LTE hashBits rateBits} ->
    SpongeParam {totalBits} hashBits

export
rateBits : SpongeParam {totalBits} hashBits -> Nat
rateBits (MkSpongeParam {totalBits} hashBits {prf1} {prf2}) =
  let p = prf in totalBits - hashBits * 2
  where
    prf : LTE (hashBits * 2) totalBits
    prf = rewrite sym prf1 in prf2

lteBy64 : (a : Nat) -> (b : Nat) -> {auto p : LTE a b}  -> LTE (a * 64) (b * 64)
lteBy64 _ _ {p} = lteCongMult 64 p

export
spongeParam256 : SpongeParam 256
spongeParam256 =
  -- 25 * 64 = 1600
  -- 8 * 64 = 512
  -- 4 * 64 = 256
  let prf1 = lteBy64 8 25 in
  let prf2 = lteBy64 4 (25 - 8) in
  MkSpongeParam 256
