module Data.Iterable

import Data.Natural
import Data.Vect

%default total
%access public export

data LazyList : Type -> Type where
  Nil : LazyList a
  (::) : a -> Lazy (LazyList a) -> LazyList a

%name LazyList a, xs, ys

fromList : List a -> LazyList a
fromList [] = []
fromList (x :: xs) = x :: fromList xs

toList : LazyList a -> List a
toList [] = []
toList (x :: xs) = x :: toList xs

append : Vect n a -> a -> Vect (S n) a
append xs x {n} =
  rewrite sym $ plusCommutative n 1 in
  xs ++ [x]

padTail : a -> Vect n a -> {auto lteNM : LTE n m} -> Vect m a
padTail {n} {m} x xs =
  rewrite sym $ eqMinusPlus m n in
  rewrite plusCommutative (m - n) n in
  xs ++ replicate (m - n) x
