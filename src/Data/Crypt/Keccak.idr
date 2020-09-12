module Data.Crypt.Keccak

import Data.Bits
import Data.Bytes
import Data.Crypt.Keccak.SpongeParam
import Data.Crypt.Keccak.Hash
import Data.Crypt.Keccak.Padding
import Data.Crypt.Keccak.Permute64
import Data.Iterable
import Data.Vect

%default total
%access export

keccak : (param : SpongeParam {totalBits = 1600}) ->
  LazyList (Bits 8) ->
  IO (LittleEndian (hashElms param * ElmBytes * 8))
keccak = hash keccakPad
