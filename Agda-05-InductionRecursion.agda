module _ where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data False : Set where
record True : Set where

_≤_ : ℕ → ℕ → Set
zero ≤ y = True
suc x ≤ zero = False
suc x ≤ suc y = x ≤ y


data SortedList : Set
head : SortedList → ℕ

data SortedList where
  [_] : ℕ → SortedList
  cons : (n : ℕ) → (ns : SortedList) → n ≤ head ns → SortedList

head [ x ] = x
head (cons n xs p) = n


example : SortedList
example = cons 1 (cons 2 (cons 9 [ 20 ] _) _) _
--example = cons 10 (cons 2 (cons 9 [ 20 ] _) _) _
