open import Data.Nat using (ℕ)
open import Data.BitVector using (BitVector)

data Value : (n : ℕ) → Set where
  unknown : ∀ {n} → Value n
  known   : ∀ {n} → BitVector n → Value n

data AnyValue : Set where
  undef : AnyValue
  sized : (size : ℕ) → Value size → AnyValue
