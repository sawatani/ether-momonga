module Data.Crypt.Keccak.SpongeParam

import Data.Bits
import Data.Nat
import Data.Natural
import Prelude.Nat

%default total
%access export

public export
LogBits : Nat
LogBits = 6

public export
ElmBits : Nat
ElmBits = 2 `pow` LogBits

public export
Elem : Type
Elem = Bits ElmBits

lteByElmBits : (a : Nat) ->
  (b : Nat) ->
  {auto p : LTE a b} ->
  LTE (a * ElmBits) (b * ElmBits)
lteByElmBits _ _ {p} = lteCongMult ElmBits p

||| Params of sponge data
data SpongeParam : {default 1600 totalBits : Nat} -> Type where
  MkSpongeParam :
    {default 25 totalElms : Nat} -> -- 25 * ElmBits = 1600
    (hashElms : Nat) -> Not (hashElms = Z) ->
    {auto prf1 : capaticyElms = hashElms * 2} ->
    {auto prf2 : LTE capaticyElms totalElms} ->
    {auto prf3 : blockElms = totalElms - capaticyElms} ->
    {auto prf4 : LTE hashElms blockElms} ->
    SpongeParam {totalBits = totalElms * ElmBits}

%name SpongeParam param, param1, param2

totalElms : SpongeParam {totalBits} -> Nat
totalElms (MkSpongeParam {totalElms} _ _) = totalElms

hashElms : SpongeParam {totalBits} -> Nat
hashElms (MkSpongeParam hashElms _) = hashElms

nonZeroHashElms : (param : SpongeParam {totalBits}) -> Not (hashElms param = 0)
nonZeroHashElms (MkSpongeParam _ nonZero) = nonZero

capaticyElms : SpongeParam {totalBits} -> Nat
capaticyElms (MkSpongeParam hashElms _ {prf1}) = hashElms * 2

hashBits : SpongeParam -> Nat
hashBits param = hashElms param * ElmBits

lteCapacityElms :
  (param : SpongeParam {totalBits}) ->
  LTE (capaticyElms param) (totalElms param)
lteCapacityElms (MkSpongeParam _ _ {prf1} {prf2}) =
  rewrite sym prf1 in prf2

blockElms : SpongeParam {totalBits} -> Nat
blockElms param = let p = lteCapacityElms param in
    totalElms param - capaticyElms param

lteHashBlockElms :
  (param : SpongeParam {totalBits}) ->
  LTE (hashElms param) (blockElms param)
lteHashBlockElms (MkSpongeParam _ _ {prf1} {prf3} {prf4}) =
  rewrite sym prf1 in
  rewrite sym prf3 in
  prf4

lteBlockElms :
  (param : SpongeParam {totalBits}) ->
  LTE (blockElms param) (totalElms param)
lteBlockElms param =
  let p = lteCapacityElms param in
  lteEqMinus (totalElms param) (capaticyElms param)

nonZeroBlockElms : (param : SpongeParam {totalBits}) -> Not (blockElms param = Z)
nonZeroBlockElms (MkSpongeParam _ nonZero {prf1} {prf3} {prf4}) =
  rewrite sym prf1 in
  rewrite sym prf3 in
  nonZeroLteNonZeroLeft prf4 nonZero

lteHashElms :
  (param : SpongeParam {totalBits}) ->
  LTE (hashElms param) (totalElms param)
lteHashElms param = lteTransitive (lteHashBlockElms param) (lteBlockElms param)

spongeParam256 : SpongeParam
spongeParam256 = MkSpongeParam 4 SIsNotZ -- 4 * ElmBits = 256

spongeParam512 : SpongeParam
spongeParam512 = MkSpongeParam 8 SIsNotZ -- 8 * ElmBits = 512
