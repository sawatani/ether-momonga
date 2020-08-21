module Data.Iterable

import Data.Natural
import Data.Vect

%default total
%access export

public export
data LazyList : Type -> Type where
  Nil : LazyList a
  (::) : a -> Lazy (LazyList a) -> LazyList a

append : Vect n a -> a -> Vect (S n) a
append xs x {n} =
  rewrite sym $ plusCommutative n 1 in
  xs ++ [x]

putTail : a -> Vect n a -> {auto lteNM : LTE n m} -> Vect m a
putTail {n} {m} x xs =
  rewrite sym $ eqMinusPlus m n in
  rewrite plusCommutative (m - n) n in
  xs ++ replicate (m - n) x
