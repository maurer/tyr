open import Data.Sum
open import Data.Product
open import Data.Bool using (true)
open import Data.Unit using (tt)
open import Data.List using ([]; [_]; _∷_)
open import Relation.Binary.PropositionalEquality
open import Arch using (ArchInfo)
open import Info
module Safety where

open import System
open import μOps
open import Disassembly
-- A value of type Steps p contains a successor for p, as well as a proof of succession
Steps : Process → Set
Steps p₀ = Σ Process (λ p₁ → p₀ ↝ p₁)

-- For every well typed process, that process is either in the halted state or can step again
progress : {p : Process} → SafeProcess p → Steps p ⊎ Halted p
-- If the machine is safe due to being halted, then it is halted
progress (typed-halted halted) = inj₂ halted
progress {p@record { insn = halt ∷ rest }} (typed-machine live x₁ x₂ safe-code-halt) =
  inj₁ (record p { halted = true; insn = rest } , ↝-μStep {p} live ↝-halt)

-- For every well typed process, taking a step results in a new well typed process
preservation : {p₀ p₁ : Process} → SafeProcess p₀ → p₀ ↝ p₁ → SafeProcess p₁
-- If the process is safe because it has stopped, no step exists
preservation (typed-halted halted) step with (live-step step) halted
... | ()
-- If the next instruction is halt, it must proceed via μStep, not fall or jump
preservation {record {insn = .(halt ∷ _)}} (typed-machine _ _ _ safe-code-halt) (↝-fall _ () _)
preservation {record {insn = .(halt ∷ _)}} (typed-machine _ _ _ safe-code-halt) (↝-jump _ _ ())
-- If the next instruction is halt, the machine becomes halted, and is safe for that reason
preservation {p@record {insn = .(halt ∷ _)}} (typed-machine _ _ _ safe-code-halt) (↝-μStep _ ↝-halt) = typed-halted tt

-- If the process p₀ is well typed, and it can evolve to some future process p, then the future process has halted or can take a step.
safety : {p₀ p : Process} → SafeProcess p₀ → p₀ ↝* p → Steps p ⊎ Halted p
safety typing trans = progress (↝*-transport preservation typing trans)
