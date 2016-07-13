open import Arch using (ArchInfo)
open import Data.List using (List)
open import Data.BitVector using (BitVector)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Nat using (ℕ)
open import Data.Bool using (T)
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open import Data.Maybe

module Disassembly (info : ArchInfo) where

open import μOps (info) using (μInsn)

Word = BitVector (ArchInfo.wordSize info)

Sema = List μInsn

Disassembly = Word → Maybe (Sema × Word)

data _⟦_↦⟨_,_⟩⟧ : Disassembly → Word → Sema → Word → Set where
  disas-known : ∀ {addr : Word} {fall : Word} {sema : Sema} → (d : Disassembly) → (d addr ≡ Maybe.just (sema , fall)) → d ⟦ addr ↦⟨ sema , fall ⟩⟧

unique-disas : ∀ {addr} {fall fall'} {sema sema'} {d}
             → d ⟦ addr ↦⟨ sema , fall ⟩⟧
             → d ⟦ addr ↦⟨ sema' , fall' ⟩⟧
             → (sema ≡ sema') × (fall ≡ fall')
unique-disas {addr} {fall} {fall'} {sema} {sema'} (disas-known d dl≡r) (disas-known .d dl≡r') =
  let r≡r' : Maybe.just (sema , fall) ≡ Maybe.just (sema' , fall')
      r≡r' = (trans (sym dl≡r) dl≡r')
      ij : Is-just (Maybe.just (sema , fall)) ≡ Is-just (Maybe.just (sema' , fall'))
      ij = {!!} 
      sf≡sf' : (sema , fall) ≡ (sema' , fall')
      sf≡sf' = cong to-witness ij -- {!to-witness!} ij
  in {!!} , {!!}
