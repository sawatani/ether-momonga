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

keccak : SpongeParam {totalBits = 1600} -> LazyList (Bits 8) -> IO (List (Bits 8))
keccak p src = do
  state <- spongeState1600 p
  let lteBlock = lteBlockElms $ param state
  let nonZero = nonZeroBlockElms $ param state
  let blocks = pad keccakPad (blockElms $ param state) {nonZero} src
  writeBlocks state blocks
  let lteHash = lteHashElms $ param state
  let hashBytes = hashElms $ param state
  elms <- read state hashBytes
  ?answer
  -- pure []
