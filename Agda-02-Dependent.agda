module _ where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A
infixr 3 _∷_

chooseType : Bool → Set
chooseType true = ℕ
chooseType false = List Bool

dependentFunction : (b : Bool) → chooseType b
dependentFunction true = 42
dependentFunction false = true ∷ false ∷ []

bad-division : ℕ → ℕ → ℕ
bad-division x zero = {!!}
bad-division x (suc y) = {!!}

data NonZero : ℕ → Set where
  non-zero : (n : ℕ) → NonZero (suc n)

division : ℕ → (denominator : ℕ) → NonZero denominator → ℕ
division x .(suc _) (non-zero y) = {!!}

is-even : ℕ → Bool
is-odd : ℕ → Bool

is-even zero = true
is-even (suc x) = is-odd x

is-odd zero = false
is-odd (suc x) = is-even x

data Even : ℕ → Set
data Odd : ℕ → Set

data Odd where
  suc-even : (n : ℕ) → Even n → Odd (suc n)
data Even where
  zero-even : Even zero
  suc-odd : (n : ℕ) → Odd n → Even (suc n)

data Either (A B : Set) : Set where
  left : A → Either A B
  right : B → Either A B

even-odd-evidence : (n : ℕ) → Either (Even n) (Odd n)
even-odd-evidence zero = left zero-even
even-odd-evidence (suc n) with even-odd-evidence n
even-odd-evidence (suc n) | left even = right (suc-even n even)
even-odd-evidence (suc n) | right odd = left (suc-odd n odd)

requires-even : (n : ℕ) → Even n → ℕ
requires-even .0        zero-even  = {!!}
requires-even .(suc _) (suc-odd n x) = {!!}

odd-is-non-zero : (n : ℕ) → Odd n → NonZero n
odd-is-non-zero .(suc _) (suc-even n x) = non-zero n
