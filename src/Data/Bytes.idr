module Data.Bytes

import Data.Bits
import Data.Vect

%default total
%access export

public export
data LittleEndian : (bits : Nat) -> Type where
  MkLittleEndian : Vect n (Bits 8) -> LittleEndian (n * 8)

lenBytes : LittleEndian bits -> Nat
lenBytes (MkLittleEndian {n} _) = n

toVect : (bs : LittleEndian bits) -> Vect (lenBytes bs) (Bits 8)
toVect (MkLittleEndian xs) = xs

namespace forVect
  ||| Hex in upper case
  toHex : Vect m (Bits n) -> String
  toHex [] = ""
  toHex (x :: xs) = toHex xs ++ bitsToHexStr x

namespace forList
  ||| Hex in upper case
  toHex : List (Bits n) -> String
  toHex [] = ""
  toHex (x :: xs) = toHex xs ++ bitsToHexStr x

toHex : LittleEndian n -> String
toHex (MkLittleEndian xs) = toHex $ reverse xs
