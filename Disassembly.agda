-- This module provides the machinery for mapping machine code to semantics and
-- fallthrough information. For the moment, this is based on a RO code segment
-- and known liftings of target addresses. Eventually, this should shift to
-- a mapping between data and instructions to allow better first class handling
-- of code.
-- FUTURE: Handle code representation rather than location
module Disassembly where

open import Info
open import μOps using (μInsn)

open import Data.List using (List)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym;
                                                         cong)
open import Data.Maybe

Sema = List μInsn

DisassemblyEntry = Sema × Word
Disassembly = Word → Maybe DisassemblyEntry

-- d ⟦ a ↦⟨ s , a′ ⟩⟧ indicates that for a disassembly d, address a is believed
-- to lift to semantics s with a fallthrough of a′
data _⟦_↦⟨_,_⟩⟧ : Disassembly → Word → Sema → Word → Set where
  -- The sole production for the disassembly predicate says that the mapped
  -- values are the output of the address lifting function
  disas-known : ∀ {addr : Word} {fall : Word} {sema : Sema} {d : Disassembly}
              → (d addr ≡ just (sema , fall))
              → d ⟦ addr ↦⟨ sema , fall ⟩⟧

-- Disassembly results are unique
-- (You cannot have two different decodings of the same address)
unique-disas : ∀ {addr} {fall fall′} {sema sema′} {d}
             → d ⟦ addr ↦⟨ sema , fall ⟩⟧
             → d ⟦ addr ↦⟨ sema′ , fall′ ⟩⟧
             → (sema ≡ sema′) × (fall ≡ fall′)
unique-disas {fall = fall} {sema = sema}
             (disas-known da≡jsf) (disas-known da≡jsf′) =
  let jsf≡jsf′ = trans (sym da≡jsf) da≡jsf′
      sf≡sf′ = cong (maybe′ (λ x → x) (sema , fall)) jsf≡jsf′
  in cong proj₁ sf≡sf′ , cong proj₂ sf≡sf′
