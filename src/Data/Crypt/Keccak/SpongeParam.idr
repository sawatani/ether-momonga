module Data.Crypt.Keccak.SpongeParam

import Data.Bits
import Data.Nat
import Data.Natural
import Data.Vect
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

public export
ElmBytes : Nat
ElmBytes = divNatNZ ElmBits 8 SIsNotZ

elemToBytes : Elem -> Vect ElmBytes (Bits 8)
elemToBytes = eToB ElmBytes
  where
    eToB : (n : Nat) -> Elem -> Vect n (Bits 8)
    eToB Z _ = []
    eToB (S k) elm =
      let b = bitsToInt $ elm `and` intToBits 255 in
      let shifted = elm `shiftRightLogical` intToBits 8 in
      intToBits b :: eToB k shifted

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

Param256 : SpongeParam
Param256 = MkSpongeParam 4 SIsNotZ

Param384 : SpongeParam
Param384 = MkSpongeParam 6 SIsNotZ

Param512 : SpongeParam
Param512 = MkSpongeParam 8 SIsNotZ

eqHash256 : (256 = hashElms Param256 * ElmBytes * 8)
eqHash256 = Refl

eqHash384 : (384 = hashElms Param384 * ElmBytes * 8)
eqHash384 = Refl

eqHash512 : (512 = hashElms Param512 * ElmBytes * 8)
eqHash512 = Refl
