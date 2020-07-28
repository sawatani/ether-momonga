module Blockchain.Ethereum.Keccak.Permute64

import Data.Bits
import Data.IOArray
import Data.Matrix
import Data.Matrix.Numeric
import Data.Natural
import Data.Vect
import Data.Primitives.Views

%default total
%access export

Elem : Type
Elem = Bits 64

rounds : Nat
rounds = 12 + 2 * 6

indexesInXY : List (Nat, Nat)
indexesInXY = do
  x <- [0..4]
  y <- [0..4]
  pure (x, y)

namespace rho
  baseMatrix : Matrix 2 2 Integer
  baseMatrix = insertRow 0 [0, 1] $ row [2, 3]

  powerBase : (t : Nat) -> Matrix 2 2 Integer
  powerBase Z = Id
  powerBase (S k) = powerBase k <> baseMatrix

  calcIndex : (t : Nat) -> Int
  calcIndex t =
    let vs = getCol 0 $ powerBase t in
    let xy = map (toIntNat . finToNat . restrict 4) vs in
    5 * (index 1 xy) + (index 0 xy)

  zipPair : (k : Nat) -> (Int, Nat)
  zipPair Z = (0, Z)
  zipPair (S t) = (calcIndex t, rotation)
    where
      rotation : Nat
      rotation = (finToNat . restrict 63) $ triNumbers $ cast t

  rotations : List (Int, Nat)
  rotations = map zipPair [0..24]

namespace pi
  mkPair : (Nat, Nat) -> Maybe (Int, Int)
  mkPair (x, y) =
    let a = 5 * y + x in
    let b = 5 * x + (modNatNZ (x + 3 * y) 5 SIsNotZ) in
    if a == b
    then Nothing
    else Just (toIntNat a, toIntNat b)

  sortedPairs : List (Int, Int)
  sortedPairs = sort $ catMaybes $ map mkPair indexesInXY

  data Chain : (fist : Int) -> (last : Int) -> Type where
    Single : (a, b : Int) -> Chain a b
    JoinHead : (a, b : Int) -> Chain b c -> Chain a c
    JoinLast : (b, c : Int) -> Chain a b -> Chain a c

  canJoinHead : (b : Int) -> Chain i j -> Dec (b = i)
  canJoinHead b chain {i} {j} = decEq b i

  canJoinLast : (a : Int) -> Chain i j -> Dec (a = j)
  canJoinLast a chain {i} {j} = decEq a j

  toList : Chain first last -> List (Int, Int)
  toList (Single first last) = [(first, last)]
  toList (JoinHead first b chain) = (first, b) :: toList chain
  toList (JoinLast b last chain) = toList chain ++ [(b, last)]

  join : Chain a b -> Chain b c -> Chain a c
  join (Single a b) y = JoinHead a b y
  join (JoinHead a b x) y = JoinHead a b $ join x y
  join (JoinLast i j x) y = join x $ JoinHead i j y

  decrease : List a -> List a
  decrease [] = []
  decrease (_ :: xs) = xs

  data Chains : Type where
    Empty : Chains
    (::) : Chain a b -> Chains -> Chains

  uniChains : Chains -> List (Int, Int)
  uniChains Empty = []
  uniChains (chain :: more) = findJoin chain more
    where
      findJoin : (x : Chain a b) -> Chains -> List (Int, Int)
      findJoin x Empty = toList x
      findJoin x {a} {b} (y :: more) =
        case canJoinHead b y of
             Yes prf => findJoin (join x (rewrite prf in y)) more
             No contra => case canJoinLast a y of
                               Yes prf => findJoin (join y (rewrite sym prf in x)) more
                               No contra => findJoin x more

  joinPairs : List (Int, Int) -> Chains -> List (Int, Int)
  joinPairs [] chains = decrease $ uniChains chains
  joinPairs ((a, b) :: xs) chains = joinPairs xs $ findJoin a b chains
    where
      findJoin : (a, b : Int) -> Chains -> Chains
      findJoin a b Empty = Single a b :: Empty
      findJoin a b (chain :: more) =
        case canJoinHead b chain of
             Yes prf => (JoinHead a b (rewrite prf in chain)) :: more
             No contra => case canJoinLast a chain of
                               Yes prf => (JoinLast a b (rewrite prf in chain)) :: more
                               No contra => chain :: findJoin a b more

  replacingPairs : List (Int, Int)
  replacingPairs = joinPairs sortedPairs Empty

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
    indexes = fromList [0..4]
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
  ) () rotations

pi : IOArray Elem -> IO ()
pi array = replace replacingPairs
  where
    replace : List (Int, Int) -> IO ()
    replace [] = pure ()
    replace ((firstIndex, secondIndex) :: xs) = do
      firstElem <- unsafeReadArray array firstIndex
      e <- unsafeReadArray array secondIndex
      unsafeWriteArray array firstIndex e
      lastIndex <- foldlM (\prevIndex, (_, index) => do
        e <- unsafeReadArray array index
        unsafeWriteArray array prevIndex e
        pure index
      ) secondIndex xs
      unsafeWriteArray array lastIndex firstElem
