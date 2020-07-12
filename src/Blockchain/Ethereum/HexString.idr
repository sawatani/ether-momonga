module Blockchain.Ethereum.HexString

import Data.Bits
import Data.List
import Data.Vect

%default total
%access private

||| Vector of bytes
||| Representing as a hex of upper case, and prefixed by "0x"
public export
data HexString : Nat -> Type where
  HexBody : Vect n Bits8 -> HexString n

export
Show (HexString n) where
  show (HexBody xs) = "0x" ++ foldl (\s, x => s ++ b8ToHexString x) "" xs

hexChars : List Char
hexChars = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
            'A', 'B', 'C', 'D', 'E', 'F']

parseEvens : (chars : List Char) -> Maybe (n ** Vect n Bits8)
parseEvens [] = Just (Z ** [])
parseEvens (x :: []) = Nothing
parseEvens (x :: y :: xs) = do a <- charToNat x
                               b <- charToNat y
                               (k ** vs) <- parseEvens xs
                               let v = natToBits {n=Z} $ (a * 16) + b
                               pure (S k ** v :: vs)
  where
    charToNat : Char -> Maybe Nat
    charToNat c = elemIndex (toUpper c) hexChars

||| Parse hex which is prefixed by "0x"
export
parseHex : String -> Maybe (n ** HexString n)
parseHex str = let chars = unpack str
               in do body <- if take 2 chars == unpack "0x"
                             then Just (drop 2 chars)
                             else Nothing
                     (n ** vect) <- parseEvens body
                     pure (n ** HexBody vect)
