open import Data.Sum
open import Data.Product

open import Arch using (ArchInfo)

module Safety (info : ArchInfo) where

open import Process info
open import Semantics info
open import Typing info

open import Data.Nat using (ℕ)
open import Data.List using (_∷_; [])

-- A value of type Steps p contains a successor for p, as well as a proof of succession
Steps : Process → Set
Steps p₀ = Σ Process (λ p₁ → p₀ ⇝ p₁)

module Intra (numTemps : ℕ) where

  open import μOps info numTemps
  open IntraInstruction {numTemps}

  IntraSteps : IntraInsnProcess → Set
  IntraSteps i₀ = Σ (IntraInsnProcess) (λ i₁ → i₀ ↝ i₁)

  IntraDone : IntraInsnProcess → Set
  IntraDone i = (Σ Process (λ p → i ↓ p))
  intraProgress : ∀ {i₀ : IntraInsnProcess} → IntraTyped i₀ → (IntraSteps i₀) ⊎ (IntraDone i₀)
  intraProgress (intra-done {p = p} downgrade x₁) = inj₂ (p , downgrade)
  intraProgress {i₀ = record {process = p; temps = t; sema = halt ∷ rest}} intra-halt =
    inj₁ (record {process = haltProcess p; temps = t; sema = []} , ↝-halt insns-of)

  intraPreservation : ∀ {i₀ i₁ : IntraInsnProcess} → IntraTyped i₀ → i₀ ↝ i₁ → IntraTyped i₁
  intraPreservation typ (↝-halt insns-of) = intra-done {!!} {!!}


-- For every well typed process, that process is either in the halted state or can step again
progress : {p : Process} → Typed p → Steps p ⊎ Halted p
--progress (typed-intra upgrade (intra-done {p = p'} downgrade pt)) = inj₁ (p' , ⇝-run upgrade IntraInstruction.↝*-nop downgrade)
--progress (typed-intra {i = record { process = process ; temps = temps ; sema = _ }} upgrade intra-halt) = {!!}
progress (typed-intra {n = n} upgrade it) with Intra.intraProgress n it
...                                          | inj₁ (i' , step) = {!!}
...                                          | inj₂ (p' , downgrade) = inj₁ (p' , ⇝-run upgrade IntraInstruction.↝*-nop downgrade)


-- For every well typed process, taking a step results in a new well typed process
preservation : {p₀ p₁ : Process} → Typed p₀ → p₀ ⇝ p₁ → Typed p₁
preservation typing transition = {!!}

-- If the process p₀ is well typed, and it can evolve to some future process p, then the future process has halted or can take a step.
safety : {p₀ p : Process} → Typed p₀ → p₀ ⇝* p → Steps p ⊎ Halted p
safety typing trans = progress (⇝*-transport preservation typing trans)
