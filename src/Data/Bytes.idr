module Data.Bytes

import Data.Bits
import Data.Vect

%default total
%access export

public export
data LittleEndian : (bits : Nat) -> Type where
  MkLittleEndian : Vect n (Bits 8) -> LittleEndian (n * 8)

namespace foundamental
  ||| Hex in lower case
  toHex : Vect m (Bits n) -> String
  toHex [] = ""
  toHex (x :: xs) = toHex xs ++ (toLower $ bitsToHexStr x)


toHex : LittleEndian n -> String
toHex (MkLittleEndian xs) = toHex $ reverse xs
