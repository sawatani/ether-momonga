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
data SpongeParam : {default 1600 totalBits : Nat} -> (hashBits : Nat) -> Type where
  MkSpongeParam :
    {default 25 totalElms : Nat} -> -- 25 * ElmBits = 1600
    (hashElms : Nat) ->
    {auto prf1 : capaticyElms = hashElms * 2} ->
    {auto prf2 : LTE capaticyElms totalElms} ->
    {auto prf3 : rateElms = totalElms - capaticyElms} ->
    {auto prf4 : LTE hashElms rateElms} ->
    SpongeParam {totalBits = totalElms * ElmBits} (hashElms * ElmBits)

%name SpongeParam param, param1, param2

totalElms : SpongeParam {totalBits} hashBits -> Nat
totalElms (MkSpongeParam {totalElms} _) = totalElms

hashElms : SpongeParam {totalBits} hashBits -> Nat
hashElms (MkSpongeParam hashElms) = hashElms

capaticyElms : SpongeParam {totalBits} hashBits -> Nat
capaticyElms (MkSpongeParam hashElms) = hashElms * 2

prfCapacityElms :
  (param : SpongeParam {totalBits} hashBits) ->
  LTE (capaticyElms param) (totalElms param)
prfCapacityElms (MkSpongeParam {totalElms} hashElms {prf1} {prf2}) =
  rewrite sym prf1 in prf2

rateElms : SpongeParam {totalBits} hashBits -> Nat
rateElms param = let p = prfCapacityElms param in
    totalElms param - capaticyElms param

prfRateElms :
  (param : SpongeParam {totalBits} hashBits) ->
  LTE (rateElms param) (totalElms param)
prfRateElms param =
  let p = prfCapacityElms param in
  lteEqMinus (totalElms param) (capaticyElms param)

spongeParam256 : SpongeParam 256
spongeParam256 = MkSpongeParam 4 -- 4 * ElmBits = 256

spongeParam512 : SpongeParam 512
spongeParam512 = MkSpongeParam 8 -- 8 * ElmBits = 512
