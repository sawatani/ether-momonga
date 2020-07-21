module Data.Natural

import Prelude.Nat

%default total
%access public export

lteEqMinus : (n : Nat) -> (m : Nat) -> {auto lteMN : LTE m n} -> LTE (n - m) n
lteEqMinus Z m = LTEZero
lteEqMinus (S k) Z = lteRefl
lteEqMinus (S k) (S j) {lteMN} =
  let lteKJ = fromLteSucc lteMN in
  let prev = lteEqMinus k j in
  lteSuccRight prev

lteEqRightMinus : (k : Nat) -> {auto lteKM : LTE k m} -> (n = m - k) -> LTE n m
lteEqRightMinus {n} {m} Z prf =
  rewrite sym (minusZeroRight m) in
  rewrite prf in lteRefl
lteEqRightMinus {m} (S k) prf = rewrite prf in lteEqMinus m (S k)
