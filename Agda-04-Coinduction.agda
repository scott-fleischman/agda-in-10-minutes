module _ where

open import Agda.Builtin.Size
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

record Stream {i : Size} (A : Set) : Set where
  coinductive
  field
    head : A
    tail : {j : Size< i} → Stream {j} A
open Stream

zeros : {i : Size} → Stream {i} ℕ
head zeros = 0
tail zeros = zeros

map : {A B : Set} → (f : A → B) → {i : Size} → Stream {i} A → Stream {i} B
head (map f xs) = f (head xs)
tail (map f xs) = map f (tail xs)

naturals : {i : Size} → Stream {i} ℕ
head naturals = 0
tail naturals = map suc naturals

zipWith : {A B C : Set} → (f : A → B → C) → {i : Size} → Stream {i} A → Stream {i} B → Stream {i} C
head (zipWith f xs ys) = f (head xs) (head ys)
tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys)

fib : {i : Size} → Stream {i} ℕ
head fib = 0
head (tail fib) = 1
tail (tail fib) = zipWith _+_ fib (tail fib)
