module Data.Crypt.Keccak

import Data.Bits
import Data.Crypt.Keccak.SpongeParam
import Data.Crypt.Keccak.SpongeState
import Data.Crypt.Keccak.Padding
import Data.Crypt.Keccak.Permute64
import Data.Vect

%default total
%access export

writeBlocks : (state : SpongeState Elem) ->
  LazyList (Vect (blockElms $ param state) Elem) ->
  {auto lte: LTE (blockElms $ param state) (totalElms $ param state)} ->
  IO ()
writeBlocks state [] = pure ()
writeBlocks state (block :: more) = do
  write state block
  writeBlocks state more

elemToBytes : (n : Nat) -> Elem -> Vect n (Bits 8)
elemToBytes Z _ = []
elemToBytes (S k) elm =
  let b = bitsToInt $ elm `and` intToBits 255 in
  let shifted = elm `shiftRightLogical` intToBits 8 in
  intToBits b :: elemToBytes k shifted

keccak : (state : SpongeState Elem) ->
  LazyList (Bits 8) ->
  IO (Vect (hashElms (param state) * ElmBytes) (Bits 8))
keccak state src =
  let lteBlock = lteBlockElms $ param state in
  let nonZero = nonZeroBlockElms $ param state in
  let blocks = pad keccakPad (blockElms $ param state) {nonZero} src in
  do
    writeBlocks state blocks
    let lteHash = lteHashElms $ param state
    elms <- read state $ hashElms $ param state
    pure $ concat $ elemToBytes ElmBytes `map` elms
