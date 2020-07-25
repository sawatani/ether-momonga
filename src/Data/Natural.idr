module Data.Natural

import Data.Bits
import Data.Fin

%default total
%access public export

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
