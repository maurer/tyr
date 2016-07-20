open import Arch using (ArchInfo)
open import Info
open ArchInfo info
module Typing where

open import Process using (Process; Halted; Live)
open import μOps

open import Data.Bool using (Bool; T)
open import Data.Vec using (Vec; _[_]≔_) renaming (_∷_ to _v∷_; [] to v[])
open import Data.List using ([_]; _∷_)
open import Data.Unit using (⊤)
open import Memory
open import Disassembly
open import Data.Maybe
open import Data.Nat using (ℕ; suc)
open import Data.Fin as Fin using (Fin)

data Kind : Set where

data Type : Set where
  τ-⊤ : Type
  τ-num : ℕ → Type

data HeapType : Set where
  ht-none : HeapType

RegisterTypes = Vec Type numRegs

data TypedRegister : Word → HeapType → Type → Set where
  reg-⊤ : ∀ {v} {ht} → TypedRegister v ht τ-⊤
  reg-num : ∀ {l : Fin (suc wordSize)} {v} {ht} → TypedRegister v ht (τ-num (Fin.toℕ l))

data TypedRegisters : ∀ {len} → Vec Word len → HeapType → Vec Type len → Set where
  regs-nil : ∀ {ht} → TypedRegisters v[] ht v[]
  regs-cons : ∀ {ht} {v} {τ} {len} {vs} {τs}
            → TypedRegister v ht τ
            → TypedRegisters {len} vs ht τs
            → TypedRegisters {suc len} (v v∷ vs) ht (τ v∷ τs)

trUpdate : ∀ {len} {regs} {ht} {rt} {rts} {v}
         → TypedRegisters {len} regs ht rts
         → TypedRegister v ht rt
         → (i : Fin len)
         → TypedRegisters {len} (regs [ i ]≔ v) ht (rts [ i ]≔ rt)
trUpdate {0} _ _ ()
trUpdate (regs-cons rt₀ rts) rt₁ Fin.zero = regs-cons rt₁ rts
trUpdate (regs-cons rt₀ rts) rt₁ (Fin.suc i) = regs-cons rt₀ (trUpdate rts rt₁ i)

data TypedHeap : Memory → HeapType → Set where
  heap-nil : ∀ {mem} → TypedHeap mem ht-none

data _,_⊢_∶_ : ∀ {l} → HeapType → RegisterTypes → Expr (τ-bv l) → Type → Set where
  eτ-imm-num : ∀ {ht} {rt} {l} {i}
             → ht , rt ⊢ imm {l} i ∶ τ-num l

data ⟨_,_⟩⇉⟨_⟩⟨_,_⟩ : HeapType → RegisterTypes → μInsn → HeapType → RegisterTypes → Set where
  steptype-reg : ∀ {ht} {rt} {idx} {trunc} {e} {τ}
               → ht , rt ⊢ e ∶ τ
               → ⟨ ht , rt ⟩⇉⟨ move (reg idx trunc) e ⟩⟨ ht , rt [ idx ]≔ τ ⟩
data SafeCode : Sema → Word → HeapType → RegisterTypes → Set where
  safe-code-halt : ∀ {fall} {insns} {ht} {rt} → SafeCode (halt ∷ insns) fall ht rt
  safe-code-step : ∀ {fall} {insn} {insns} {ht₀ ht₁} {rt₀ rt₁}
                 → ⟨ ht₀ , rt₀ ⟩⇉⟨ insn ⟩⟨ ht₁ , rt₁ ⟩
                 → SafeCode insns fall ht₁ rt₁
                 → SafeCode (insn ∷ insns) fall ht₀ rt₀

data SafeProcess : Process → Set where
  typed-halted : ∀ {p}
               → Halted p
               → SafeProcess p
  typed-machine : ∀ {p} {registerTypes} {heapType}
                → Live p
                → TypedHeap (Process.memory p) heapType
                → TypedRegisters (Process.registers p) heapType registerTypes        
                → SafeCode (Process.insn p) (Process.fall p) heapType registerTypes
                → SafeProcess p

