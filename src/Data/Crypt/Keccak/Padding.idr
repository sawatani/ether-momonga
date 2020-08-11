module Data.Crypt.Keccak.Padding

import Data.Bits
import Data.Natural
import Data.Vect
import Data.Crypt.Keccak.SpongeParam

%default total
%access export

ElmBytes : Nat
ElmBytes = divNatNZ ElmBits 8 SIsNotZ

loadBytes : (n : Nat) -> List a ->
  Either (m : Nat ** (Vect m a, LT m n)) (List a, Vect n a)
loadBytes Z xs = Right (xs, [])
loadBytes (S k) [] = Left (Z ** ([], LTESucc LTEZero))
loadBytes (S k) (x :: xs) =
  case loadBytes k xs of
       Left (m ** (ys, ltMK)) => Left (S m ** (x :: ys, LTESucc ltMK))
       Right (r, ys) => Right (r, x :: ys)

combine : Vect n (Bits 8) -> {auto lteN : LTE n ElmBytes} -> Elem
combine [] = intToBits 0
combine {n = S k} (v :: vs) {lteN} =
  let extended = zeroExtend v in
  let shifted = extended `shiftLeft` (intToBits . fromNat $ k * 8) in
  let lteK = lteSuccLeft lteN in
  shifted `plus` combine vs

data PadByte : Type where
  MkPad : Bits 8 -> PadByte

keccakPad : PadByte
keccakPad = MkPad $ intToBits 1

sha3Pad : PadByte
sha3Pad = MkPad $ intToBits 6

loadElem : PadByte -> List (Bits 8) -> Either Elem (List (Bits 8), Elem)
loadElem (MkPad pad) xs =
  case loadBytes ElmBytes xs of
       Right (r, ys) => Right (r, combine ys)
       Left (m ** (ys, ltM)) =>
         let ps = zeroExtend pad `shiftLeft` (intToBits . fromNat $ m * 8) in
         let lteM = lteSuccLeft ltM in
         Left (combine ys `plus` ps)

loadElems : PadByte -> (n : Nat) -> List (Bits 8) ->
  Either (m : Nat ** (Vect m Elem, LTE m n)) (List (Bits 8), Vect n Elem)
loadElems (MkPad x) Z xs = Right (xs, [])
loadElems (MkPad x) (S k) [] = Left (Z ** ([], LTEZero))
loadElems padByte (S k) xs =
  case loadElems padByte k xs of
       Left (m ** (ys, lte)) => Left (m ** (ys, lteSuccRight lte))
       Right (rs, es) =>
         case loadElem padByte rs of
              Left e => Left ((S k) ** ((e :: es), lteRefl))
              Right (remaining, e) => Right (remaining, e :: es)

putTail : a -> Vect n a -> {auto lteNM : LTE n m} -> Vect m a
putTail {n} {m} x xs =
  rewrite sym $ eqMinusPlus m n in
  rewrite plusCommutative (m - n) n in
  xs ++ replicate (m - n) x

setLastBit : Vect (S k) Elem -> Vect (S k) Elem
setLastBit {k} xs =
  let fi = restrict (pred ElmBits) $ fromNat ElmBits - 1 in
  let e = setBit fi $ last xs in
  rewrite sym $ plusCommutative k 1 in
  init xs ++ [e]

pad : PadByte -> List (Bits 8) -> List (Vect (S k) Elem)
pad {k} (MkPad pad) [] =
  let one = zeroExtend pad :: replicate k (intToBits 0) in
  [setLastBit one]
pad {k} padByte xs =
  case loadElems padByte (S k) xs of
       Right (remaining, es) => es :: pad padByte remaining
       Left (m ** (ys, lte)) =>
         let es = putTail (intToBits 0) ys in
         [setLastBit es]
