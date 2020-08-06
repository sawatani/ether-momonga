module Data.Crypt.LFSR

import Data.Bits
import Data.Fin
import Data.Vect

%default total
%access export

value1 : {n : Nat} -> {auto nonZero : S k = n} -> Bits n
value1 {n} = intToBits 1

data Taps : (n : Nat) -> Type where
  MkTaps: {n : Nat} -> {auto nonZero : S k = n} -> (taps : Bits n) -> Taps n

mkTaps : (n: Nat) -> {auto nonZero : S k = n} -> Vect m (Fin n) -> {auto prf : LTE m n} -> Taps n
mkTaps n xs = MkTaps $ foldr setBit value1 xs

%hint
taps2 : Taps 2
taps2 = mkTaps 2 [1]

%hint
taps3 : Taps 3
taps3 = mkTaps 3 [2]

%hint
taps4 : Taps 4
taps4 = mkTaps 4 [3]

%hint
taps5 : Taps 5
taps5 = mkTaps 5 [3]

%hint
taps6 : Taps 6
taps6 = mkTaps 6 [5]

%hint
taps7 : Taps 7
taps7 = mkTaps 7 [6]

%hint
taps8 : Taps 8
taps8 = mkTaps 8 [6, 5, 4]

output : Bits n -> {auto nonZero : S k = n} -> Bool
output a {k} {nonZero} = restrict k 0 `getBit` rewrite nonZero in a

next : {n : Nat} -> Bits n -> {auto tp : Taps n} -> {auto nonZero : S k = n} -> Bits n
next x {k} {tp = MkTaps taps} {nonZero} =
  let y = shiftLeft x value1 in
  let most = getBit (restrict k $ fromNat k) (rewrite nonZero in x) in
  if most then y `xor` taps else y
