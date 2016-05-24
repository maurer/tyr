open import Arch using (ArchInfo)

module Semantics (info : ArchInfo) where

open import Process info using (Process; ArchValue)
open import Value
open import Data.Nat using (ℕ; _⊔_)
open import Data.Vec as Vec using (Vec)
open import Data.List using (List)
open import Data.Fin using (Fin)
open import Disassembly info
open import Data.Product using (_,_)

import μOps info as μOps

module IntraInstruction {numTemps : ℕ} where

  open μOps numTemps

  record IntraInsnProcess : Set where
    field
      process  : Process 
      temps    : Vec AnyValue numTemps
      sema     : List μInsn

  data _↝_ : IntraInsnProcess → IntraInsnProcess → Set where
    
  data _↝*_ : IntraInsnProcess → IntraInsnProcess → Set where
    ↝*-nop : ∀ {i} → i ↝* i
    ↝*-extend : ∀ {i₀ i₁ i₂}
              → i₀ ↝* i₁ → i₁ ↝ i₂ → i₀ ↝* i₂

  upgrade : List μInsn → Process → IntraInsnProcess
  upgrade sema p = record { process = p; temps = Vec.replicate undef; sema = sema}

  downgrade : IntraInsnProcess → Process
  downgrade iip = IntraInsnProcess.process iip

  data Done : IntraInsnProcess → Set where
    done-empty : ∀ {p} {t} → Done (record { process = p ; temps = t ; sema = List.[] })

  data _↓_ : IntraInsnProcess → Process → Set where
    ↓-done : ∀ {i} → Done i → i ↓ (IntraInsnProcess.process i)

  data _↑_ : Process → IntraInsnProcess → Set where
    ↑-static : ∀ {p} {sema} → (Process.disassembly p) ⟦ (Process.pc p) ↦⟨ numTemps , sema ⟩⟧ → p ↑ (upgrade sema p)

open IntraInstruction

data _⇝_ : Process → Process → Set where
  ⇝-run : ∀ {p₀ p₁ : Process}
            {numTemps : ℕ}
            {i₀ i₁ : IntraInsnProcess {numTemps}}
          → p₀ ↑ i₀
          → i₀ ↝* i₁
          → i₁ ↓ p₁
          → p₀ ⇝ p₁

data _⇝*_ : Process → Process → Set where
  ⇝*-nop : {p : Process} → p ⇝* p
  ⇝*-extend : {p₀ p₁ p₂ : Process} → p₀ ⇝* p₁ → p₁ ⇝ p₂ → p₀ ⇝* p₂

-- If we can move a property across ⇝, we can move it across ⇝*. 
⇝*-transport : {p₀ p₁ : Process} → {P : Process → Set} → (step : {p₀ p₁ : Process} → P p₀ → p₀ ⇝ p₁ → P p₁) → P p₀ → p₀ ⇝* p₁ → P p₁
⇝*-transport _ base ⇝*-nop = base
⇝*-transport step base (⇝*-extend trans x) = step (⇝*-transport step base trans) x
