module Blockchain.Ethereum.Keccak.Permute64

import Data.Bits
import Data.IOArray
import Data.Natural
import Data.Vect

%default total
%access export

Elem : Type
Elem = Bits 64

rounds : Nat
rounds = 12 + 2 * 6

rotationConstants : Vect 25 (Int, Nat)
rotationConstants = reverse $ triangles 25
  where
    tri : (k : Nat) -> (Int, Nat)
    tri Z = (0, Z)
    tri i@(S t) = (cast i, t)
    triangles : (n : Nat) -> Vect n (Int, Nat)
    triangles Z = []
    triangles (S k) = tri k :: triangles k

theta : IOArray Elem -> IO ()
theta array = do
    leftColumn <- xors
    let rightColumn = map (`rotateL` 1) leftColumn
    foldlM (\_, i => do
      e <- unsafeReadArray array i
      let x = cast i
      let leftX = restrict 4 (x + 4) `index` leftColumn
      let rightX = restrict 4 (x + 1) `index` rightColumn
      let e' = (e `xor` leftX) `xor` rightX
      unsafeWriteArray array i e'
    ) () [0..24]
  where
    indexes : Vect 5 Int
    indexes = [0, 1, 2, 3, 4]
    xorColumn : Int -> IO Elem
    xorColumn x = do
      ys <- traverse (\y => unsafeReadArray array $ 5 * y + x) indexes
      pure $ foldr1 xor ys
    xors : IO (Vect 5 Elem)
    xors = traverse xorColumn indexes

rho : IOArray Elem -> IO ()
rho array = foldlM (\_, (i, s) => do
    e <- unsafeReadArray array i
    let e' = e `rotateL` s
    unsafeWriteArray array i e'
  ) () rotationConstants
