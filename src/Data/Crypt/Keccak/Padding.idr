module Data.Crypt.Keccak.Padding

import Data.Bits
import Data.Crypt.Keccak.SpongeParam
import Data.Natural
import Data.Iterable
import Data.Vect

%default total
%access export

data PadByte : Type where
  MkPad : Bits 8 -> PadByte

keccakPad : PadByte
keccakPad = MkPad $ intToBits 1

sha3Pad : PadByte
sha3Pad = MkPad $ intToBits 6

ElmBytes : Nat
ElmBytes = divNatNZ ElmBits 8 SIsNotZ

combine : Vect n (Bits 8) -> {auto lteN : LTE n ElmBytes} -> Elem
combine {n} xs = combine' xs {lteM = lteRefl}
  where
    combine' : Vect m (Bits 8) -> {auto lteM : LTE m n} -> Elem
    combine' [] = intToBits 0
    combine' {m = S k} (v :: vs) {lteM} =
      let extended = zeroExtend v in
      let shifted = extended `shiftLeft` (intToBits . fromNat $ (n - S k) * 8) in
      let lteK = lteSuccLeft lteM in
      shifted `plus` combine' vs

setLastBit : Vect (S k) Elem -> Vect (S k) Elem
setLastBit {k} xs =
  let fi = restrict (pred ElmBits) $ fromNat ElmBits - 1 in
  let e = setBit fi $ last xs in
  init xs `append` e

loadAndPad :
  PadByte ->
  (nonZero : Not (n = Z)) ->
  LazyList (Bits 8) ->
  (building : Vect nB (Bits 8)) ->
  (adding : Vect nA Elem) ->
  {auto ltB : LT nB ElmBytes} ->
  {auto ltA : LT nA n} ->
  LazyList (Vect n Elem)
loadAndPad _ {n = Z} nonZero _ _ _ = void $ nonZero Refl
loadAndPad (MkPad pad) {n = (S k)} nonZero [] building adding {ltB} {nB} =
  let ps = zeroExtend pad `shiftLeft` (intToBits . fromNat $ nB * 8) in
  let lteB = lteSuccLeft ltB in
  let e = combine building `plus` ps in
  let added = adding `append` e in
  let es = padTail (intToBits 0) added in
  [setLastBit es]
loadAndPad padByte {n = (S k)} nonZero (x :: xs) building adding {ltA} {nB} {nA} =
  let addedBuilding = building `append` x in
  case isLTE (S (S nB)) ElmBytes of
       (Yes prf) => loadAndPad padByte nonZero xs addedBuilding adding
       (No _) =>
         let e = combine addedBuilding in
         let added = adding `append` e in
         case isLTE (S (S nA)) (S k) of
              (Yes prf) => loadAndPad padByte nonZero xs [] added
              (No contra) =>
                let eqN = lteNotLteSuccEq ltA contra in
                (rewrite sym eqN in added) :: loadAndPad padByte nonZero xs [] []

pad : PadByte -> (nonZero : Not (n = Z)) ->
  LazyList (Bits 8) -> LazyList (Vect n Elem)
pad _ nonZero _ {n=Z} = void $ nonZero Refl
pad padByte nonZero xs {n=(S k)} = loadAndPad padByte nonZero xs [] []
