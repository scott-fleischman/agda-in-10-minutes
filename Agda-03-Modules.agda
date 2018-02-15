module _ where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

module Container (A : Set) where
  data List : Set where
    [] : List
    _∷_ : A → List → List

  length : List → ℕ
  length []       = zero
  length (x ∷ xs) = suc (length xs)

  data Vector : ℕ → Set where
    [] :                              Vector zero
    _∷_ : A → {n : ℕ} → Vector n → Vector (suc n)

  repeat : (n : ℕ) → A → Vector n
  repeat zero x = []
  repeat (suc n) x = x ∷ repeat n x

vmap : {A B : Set} → (A → B) → {n : ℕ} → Container.Vector A n → Container.Vector B n
vmap f Container.[] = Container.[]
vmap f (x Container.∷ xs) = f x Container.∷ vmap f xs

module M (A : Set) where
  open Container

  Matrix : Set → ℕ → ℕ → Set
  Matrix A m n = Vector (Vector A n) m

  go : ∀ {m A n} →
     Vector A n → Vector (Vector A m) n → Vector (Vector A (suc m)) n
  go [] [] = []
  go (x ∷ xs) (xss ∷ xss₁) = (x ∷ xss) ∷ go xs xss₁

  transpose : {A : Set} → (m n : ℕ) → Matrix A m n → Matrix A n m
  transpose zero n xss = repeat _ n []
  transpose (suc m) n (xs ∷ xss) = go xs (transpose m n xss)
