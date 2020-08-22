module Data.Natural

import Data.Bits
import Data.Fin
import Data.Primitives.Views
import Decidable.Order

%default total
%access public export

notLteGt : Not (LTE m n) -> GT m n -- LTE (S n) m
notLteGt {m = Z} {n = Z} notLTE = absurd $ notLTE lteRefl
notLteGt {m = (S k)} {n = Z} _ = LTESucc LTEZero
notLteGt {m = Z} {n = (S k)} notLTE = absurd $ notLTE LTEZero
notLteGt {m = (S j)} {n = (S k)} notLTE =
  case isLTE j k of
       (Yes prf) => absurd $ notLTE $ LTESucc prf
       (No contra) => LTESucc $ notLteGt contra

lteNotLteSuccEq : LTE m n -> Not (LTE (S m) n) -> m = n
lteNotLteSuccEq {m} {n} lteM notLTE =
  let gt = notLteGt notLTE in
  let lteN = fromLteSucc gt in
  antisymmetric m n lteM lteN

nonZeroLteNonZeroLeft : LTE m n -> Not (m = 0) -> Not (n = 0)
nonZeroLteNonZeroLeft LTEZero sj = absurd $ sj Refl
nonZeroLteNonZeroLeft (LTESucc _) _ = SIsNotZ

eqMinusPlus : (n : Nat) -> (m : Nat) -> {auto lteMN: LTE m n} -> n - m + m = n
eqMinusPlus n Z = rewrite minusZeroRight n in rewrite plusZeroRightNeutral n in Refl
eqMinusPlus (S k) (S j) {lteMN} =
  let lteJK = fromLteSucc lteMN in
  rewrite sym $ plusSuccRightSucc (k - j) j in
  let prev = eqMinusPlus k j in
  eqSucc (k - j + j) k prev

lteEqMinus : (n : Nat) -> (m : Nat) -> {auto lteMN : LTE m n} -> LTE (n - m) n
lteEqMinus Z m = LTEZero
lteEqMinus (S k) Z = lteRefl
lteEqMinus (S k) (S j) {lteMN} =
  let lteKJ = fromLteSucc lteMN in
  let prev = lteEqMinus k j in
  lteSuccRight prev

lteEqRightMinus : {auto lteKM : LTE k m} -> (n = m - k) -> LTE n m
lteEqRightMinus {m} {k} prf = rewrite prf in lteEqMinus m k

rotateL : {n : Nat} -> Bits n -> Nat -> Bits n
rotateL bits Z = bits
rotateL {n = Z} bits _ = bits
rotateL {n = n@(S _)} bits m@(S _) =
  let i = toIntegerNat $ modNatNZ m n SIsNotZ in
  let limit = toIntegerNat n in
  let left = intToBits i in
  let right = intToBits $ limit- i in
  shiftLeft bits left `or` shiftRightLogical bits right

||| Triangular Numbers
||| start from 1 at 0
||| fomula n := (n + 1) * (n + 2) / 2
triNumbers : Integer -> Integer
triNumbers n with (divides n 2)
  triNumbers ((2 * div) + rem) | (DivBy prf) =
    case rem of
         0 => (2 * div + 1) * (div + 1)
         _ => (div + 1) * (2 * div + 3)
