open import Arch using (ArchInfo)
open import Data.List using (List)
open import Data.BitVector using (BitVector)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Nat using (ℕ)
import Data.List.Any
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as PropEq
import Level

module Disassembly (info : ArchInfo) where

open import μOps (info) using (μInsn)

Word = BitVector (ArchInfo.wordSize info)

Sema = Σ ℕ (λ numTemps → List (μInsn numTemps))

Disassembly = List (Word × Sema)

disasmSetoid : Setoid Level.zero Level.zero
disasmSetoid = record { Carrier = Word × Sema ; _≈_ = PropEq._≡_ ; isEquivalence = PropEq.isEquivalence }

open Data.List.Any.Membership disasmSetoid using (_∈_)

data _⟦_↦⟨_⟩⟧ : Disassembly → Word → Sema → Set where
  disas-known : ∀ {addr : Word} {sema : Sema} → (d : Disassembly) → ((addr , sema) ∈ d) → d ⟦ addr ↦⟨ sema ⟩⟧
