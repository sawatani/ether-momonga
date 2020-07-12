module Blockchain.Ethereum.Address

import Data.Vect
import Blockchain.Ethereum.HexString

%default total
%access private

AddrHex : Type
AddrHex = HexString 20

export
data Address : Type where
  AddrBody : (src : String) -> (hex : AddrHex) -> Address

Show Address where
  show (AddrBody src hex) = src

export
getBytes : Address -> Vect 20 Bits8
getBytes (AddrBody src (HexBody xs)) = xs

export
parseAddress : String -> Maybe Address
parseAddress str = parseHex str >>= mkAddr
  where
    mkAddr : (n : Nat ** HexString n) -> Maybe Address
    mkAddr (x ** hex) with (x `cmp` 20)
      mkAddr (_ ** hex) | CmpEQ = Just $ AddrBody str hex
      mkAddr _ | _ = Nothing

