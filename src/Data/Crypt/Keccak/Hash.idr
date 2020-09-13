module Data.Crypt.Keccak.Hash

import Data.Bits
import Data.Bytes
import Data.IOArray
import Data.Vect
import Data.Natural
import Data.Crypt.Keccak.SpongeParam
import Data.Crypt.Keccak.Padding
import Data.Crypt.Keccak.Permute64
import Data.Iterable

%default total
%access export

private
mkArray : SpongeParam -> IO (IOArray Elem)
mkArray param = newArray (fromNat $ totalElms param) $ intToBits 0

private
write : IOArray Elem -> Vect n Elem -> IO ()
write array xs = xorElem 0 xs
  where
    xorElem : (i : Int) -> Vect j Elem -> IO ()
    xorElem i [] = pure ()
    xorElem i (x :: xs) = do
      y <- unsafeReadArray array i
      unsafeWriteArray array i (x `xor` y)
      xorElem (i + 1) xs

private
read : IOArray Elem -> (n : Nat) -> IO (Vect n Elem)
read array n = pick n
  where
    pick : (j : Nat) -> IO $ Vect j Elem
    pick Z = pure []
    pick m@(S k) = do
      let i = toIntNat n - toIntNat m
      e <- unsafeReadArray array i
      sucs <- pick k
      pure $ e :: sucs

private
permute : IOArray Elem -> IO ()
permute array = roundAll array

private
writeBlocks : IOArray Elem -> LazyList (Vect n Elem) -> IO ()
writeBlocks array [] = pure ()
writeBlocks array (block :: more) = do
  write array block
  permute array
  writeBlocks array more

hash : PadByte ->
  (param : SpongeParam) ->
  LazyList (Bits 8) ->
  IO (LittleEndian (hashElms param * ElmBytes * 8))
hash padByte param src = do
  array <- mkArray param
  let blocks = pad padByte (nonZeroBlockElms param) src
  writeBlocks array blocks
  elms <- read array $ hashElms param
  let bytes = concat $ elemToBytes `map` elms
  pure $ MkLittleEndian bytes
