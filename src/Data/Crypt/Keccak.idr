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

keccak256 : LazyList (Bits 8) -> IO (LittleEndian 256)
keccak256 src = rewrite eqHash256 in keccak Param256 src

keccak384 : LazyList (Bits 8) -> IO (LittleEndian 384)
keccak384 src = rewrite eqHash384 in keccak Param384 src

keccak512 : LazyList (Bits 8) -> IO (LittleEndian 512)
keccak512 src = rewrite eqHash512 in keccak Param512 src
