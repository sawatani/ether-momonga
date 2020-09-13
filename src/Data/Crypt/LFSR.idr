module Data.Crypt.LFSR

import Data.Bits
import Data.Fin
import Data.Vect

%default total
%access export

value1 : Bits (S k)
value1 = intToBits 1

data Taps : Nat -> Type where
  MkTaps: (taps : Bits (S k)) -> Taps (S k)

private
mkTaps : Vect m (Fin (S k)) -> {auto prf : LTE m (S k)} -> Taps (S k)
mkTaps xs = MkTaps $ foldr setBit value1 xs

%hint
taps2 : Taps 2
taps2 = mkTaps [1]

%hint
taps3 : Taps 3
taps3 = mkTaps [2]

%hint
taps4 : Taps 4
taps4 = mkTaps [3]

%hint
taps5 : Taps 5
taps5 = mkTaps [3]

%hint
taps6 : Taps 6
taps6 = mkTaps [5]

%hint
taps7 : Taps 7
taps7 = mkTaps [6]

%hint
taps8 : Taps 8
taps8 = mkTaps [6, 5, 4]

output : Bits (S k) -> Bool
output a {k} = restrict k 0 `getBit` a

next : Bits (S k) -> {auto tp : Taps (S k)} -> Bits (S k)
next x {k} {tp = MkTaps taps} =
  let y = shiftLeft x value1 in
  let most = getBit (restrict k $ fromNat k) x in
  if most then y `xor` taps else y
