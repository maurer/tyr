open import Data.Nat using (ℕ; _≤_; decTotalOrder; z≤n)
open import Data.BitVector using (BitVector)
open import Data.Vec using ([])
open import Data.Fin as Fin using (Fin)

data Value : (n : ℕ) → Set where
  -- Defines the lower m bits of an n-bit value. Useful for partially defined register values
  some-known : ∀ {m n : ℕ} {lt : m ≤ n} → BitVector m → Value n

data SizedValue : Set where
  sized : (size : ℕ) → Value size → SizedValue

data AnyValue : Set where
  undef-size : AnyValue
  known-size : SizedValue → AnyValue

BitValue : Set
BitValue = Value 1

open import Relation.Binary
trans-ℕ : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
trans-ℕ = DecTotalOrder.trans decTotalOrder

≡-≤-ℕ : ∀ {n} → n ≤ n
≡-≤-ℕ = DecTotalOrder.refl decTotalOrder

mergeValue : ∀ {m n : ℕ} {lt : m ≤ n} → (base : Value n) → (update : Value m) → Value n
--TODO actually merge value
mergeValue {lt = lt} (some-known {defined₀} {size₀} bitsBase) (some-known {defined₁} {size₁} {lt'} bitsUpdate) = some-known {lt = trans-ℕ lt' lt} bitsUpdate

undef : ∀ {n} → Value n
undef = some-known {lt = z≤n} []

--TODO INCOMPLETE
subVal : ∀ {n} → Value n → (i : Fin n) → Value (Fin.toℕ i)
subVal _ i = some-known {lt = z≤n} []

data Concrete : ∀ {n} → Value n → BitVector n → Set where
  concrete : ∀ {n} {bv : BitVector n} → Concrete (some-known {lt = ≡-≤-ℕ} bv) bv
