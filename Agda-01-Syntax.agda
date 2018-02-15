module _ where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

_&&_ : Bool → Bool → Bool
true && y = y
false && y = false

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A
infixr 3 _∷_

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys
