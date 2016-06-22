open import Data.Sum
open import Data.Product

open import Arch using (ArchInfo)

module Safety (info : ArchInfo) where

open import System info

-- A value of type Steps p contains a successor for p, as well as a proof of succession
Steps : Process → Set
Steps p₀ = Σ Process (λ p₁ → p₀ ⇝ p₁)

-- For every well typed process, that process is either in the halted state or can step again
progress : {p : Process} → Typed p → Steps p ⊎ Halted p
progress ()

-- For every well typed process, taking a step results in a new well typed process
preservation : {p₀ p₁ : Process} → Typed p₀ → p₀ ⇝ p₁ → Typed p₁
preservation ()

-- If the process p₀ is well typed, and it can evolve to some future process p, then the future process has halted or can take a step.
safety : {p₀ p : Process} → Typed p₀ → p₀ ⇝* p → Steps p ⊎ Halted p
safety typing trans = progress (⇝*-transport preservation typing trans)
