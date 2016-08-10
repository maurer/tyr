open import Arch using (ArchInfo)
open import Info
open ArchInfo info
module Typing where

open import Process using (Process; Halted; Live)
open import μOps

open import Data.Bool using (Bool; T)
open import Data.Vec using (Vec; _[_]≔_) renaming (_∷_ to _v∷_; [] to v[])
open import Data.List using ([_]; _∷_; List; [])
open import Data.Unit using (⊤)
open import Memory
open import Disassembly
open import Data.Maybe
open import Data.Nat using (ℕ; suc)
open import Data.Fin as Fin using (Fin)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.BitVector using (BitVector)
open import Semantics using (mergeVec)
open import Relation.Binary.PropositionalEquality renaming (setoid to peSetoid)
import Data.List.Any

data Kind : Set where

data Type : Set
RegisterTypes = Vec Type numRegs
data Type where
  τ-⊤ : Type
  τ-num : ℕ → Type
  τ-code : RegisterTypes → Type
  τ-ptr : Type → Type

data HeapLoc : Set where
  -- Constant address, as for ro code segment or a global
  hl-const : Word → HeapLoc
  -- Abstract address, could live anywhere
  hl-abs   : ℕ → HeapLoc

HeapEntry = HeapLoc × Type
HeapType = List HeapEntry

open Data.List.Any.Membership (peSetoid HeapEntry) using (_∈_)

data TypedRegister : Word → HeapType → Disassembly → Type → Set
data TypedRegisters : ∀ {len} → Vec Word len → HeapType → Disassembly → Vec Type len → Set
data _⊢_~_ : ∀ {l} → HeapType → BitVector l → Type → Set
data _,_⊢_∶_ : ∀ {l} → HeapType → RegisterTypes → Expr (τ-bv l) → Type → Set
data ⟨_,_⟩⇉⟨_⟩⟨_,_⟩ : HeapType → RegisterTypes → μInsn → HeapType → RegisterTypes → Set
data SafeCode : Sema → Word → HeapType → RegisterTypes → Set
data _⊢_⇒_ : HeapType → Word → Type → Set

data _⊢_⇒_ where
  const-⇒ : ∀ {a} {τ} {ht}
          → ((hl-const a) , τ) ∈ ht
          → ht ⊢ a ⇒ τ

data _⊢_~_ where
  ~⊤ : ∀ {l} {v : BitVector l} {ht}
     → ht ⊢ v ~ τ-⊤
  ~num : ∀ {l} {v : BitVector l} {ht}
       → ht ⊢ v ~ τ-num l
  ~ptr : ∀ {v : Word} {ht} {τ}
       → ht ⊢ v ⇒ τ
       → ht ⊢ v ~ τ-ptr τ

data TypedRegister where
  reg-direct : ∀ {l} {v : BitVector l} {lt} {ht} {d} {τ} {b}
             → ht ⊢ v ~ τ 
             → TypedRegister (mergeVec {lt = lt} b v) ht d τ
  --TODO support truncated registers 
  reg-code : ∀ {v} {insns} {fall} {ht} {d} {rt}
           → d ⟦ v ↦⟨ insns , fall ⟩⟧
           → SafeCode insns fall ht rt
           → TypedRegister v ht d (τ-ptr (τ-code rt))

data TypedRegisters where
  regs-nil : ∀ {ht} {d} → TypedRegisters v[] ht d v[]
  regs-cons : ∀ {ht} {v} {τ} {len} {vs} {τs} {d}
            → TypedRegister v ht d τ
            → TypedRegisters {len} vs ht d τs
            → TypedRegisters {suc len} (v v∷ vs) ht d (τ v∷ τs)

data _,_⊢_∶_ where
  eτ-imm-num : ∀ {ht} {rt} {l} {i}
             → ht , rt ⊢ imm {l} i ∶ τ-num l
  eτ-imm-ht : ∀ {ht} {rt} {i} {τ}
            → (hl-const i , τ) ∈ ht
            → ht , rt ⊢ imm i ∶ τ-ptr τ 

data ⟨_,_⟩⇉⟨_⟩⟨_,_⟩ where
  steptype-reg : ∀ {ht} {rt} {idx} {trunc} {e} {τ}
               → ht , rt ⊢ e ∶ τ
               → ⟨ ht , rt ⟩⇉⟨ move (reg idx trunc) e ⟩⟨ ht , rt [ idx ]≔ τ ⟩

data SafeCode where
  safe-code-halt : ∀ {fall} {insns} {ht} {rt} → SafeCode (halt ∷ insns) fall ht rt
  safe-code-step : ∀ {fall} {insn} {insns} {ht₀ ht₁} {rt₀ rt₁}
                 → ⟨ ht₀ , rt₀ ⟩⇉⟨ insn ⟩⟨ ht₁ , rt₁ ⟩
                 → SafeCode insns fall ht₁ rt₁
                 → SafeCode (insn ∷ insns) fall ht₀ rt₀
  safe-code-fall : ∀ {fall} {ht} {rt}
                 → ht , rt ⊢ imm fall ∶ τ-ptr (τ-code rt)
                 → SafeCode [] fall ht rt
  safe-code-jump : ∀ {fall} {ht} {rt} {e} {insns}
                 → ht , rt ⊢ e ∶ τ-ptr (τ-code rt)
                 → SafeCode (jmp e ∷ insns) fall ht rt

trUpdate : ∀ {len} {regs} {ht} {rt} {rts} {v} {d}
         → TypedRegisters {len} regs ht d rts
         → TypedRegister v ht d rt
         → (i : Fin len)
         → TypedRegisters {len} (regs [ i ]≔ v) ht d (rts [ i ]≔ rt)
trUpdate {0} _ _ ()
trUpdate (regs-cons rt₀ rts) rt₁ Fin.zero = regs-cons rt₁ rts
trUpdate (regs-cons rt₀ rts) rt₁ (Fin.suc i) = regs-cons rt₀ (trUpdate rts rt₁ i)


data PartialTypedHeap : Memory → Disassembly → HeapType → HeapType → Set where
  heap-nil   : ∀ {mem} {disas} {ht} → PartialTypedHeap mem disas ht []
  --TODO with proper structuring, heap-const and heap-const-code could be merged
  --Specifically, if we can treat code as first-class rather than something that
  --will only ever be pointed at, ht ⊢ v ~ τ-code rt would be a possible judgement
  heap-const : ∀ {mem} {disas} {ht} {ht₀} {k} {l} {v} {τ}
             → PartialTypedHeap mem disas ht ht₀
             → Read mem k l v
             → ht ⊢ v ~ τ
             → PartialTypedHeap mem disas ht (((hl-const k) , τ) ∷ ht₀)
  heap-const-code : ∀ {mem} {disas} {ht} {ht₀} {k} {insns} {fall} {rt}
                  → PartialTypedHeap mem disas ht ht₀
                  → disas ⟦ k ↦⟨ insns , fall ⟩⟧
                  → SafeCode insns fall ht rt
                  → PartialTypedHeap mem disas ht (((hl-const k) , τ-code rt) ∷ ht₀)

data TypedHeap : Memory → Disassembly → HeapType → Set where
  partial-done : ∀ {mem} {disas} {ht}
               → PartialTypedHeap mem disas ht ht
               → TypedHeap mem disas ht



record SafeHeapCode (disas : Disassembly) (pc : Word) (ht : HeapType) (rt : RegisterTypes): Set where
  field
    fall  : Word
    insn  : List μInsn
    safe  : SafeCode insn fall ht rt
    dis-i : disas ⟦ pc ↦⟨ insn , fall ⟩⟧

safeHeapCode' : ∀ {ht₀} {ht} {mem} {disas} {rt} {pc}
              → PartialTypedHeap mem disas ht₀ ht
              → (hl-const pc , τ-code rt) ∈ ht
              → SafeHeapCode disas pc ht₀ rt
--If this entry is the one for the code pointer, heap-const can't have generated it
safeHeapCode' {rt = rt} (heap-const x x₁ ~⊤) (Data.List.Any.here px) with px
... | ()
safeHeapCode' {rt = rt} (heap-const x₁ x₂ ~num) (Data.List.Any.here px) with px
... | ()
safeHeapCode' (heap-const _ _ (~ptr _)) (Data.List.Any.here px) with px
... | ()
safeHeapCode' (heap-const-code {k = k} {insns = insns} {fall = fall} _ d s) (Data.List.Any.here refl) = record { fall = fall ; insn = insns ; safe = s ; dis-i = d }

safeHeapCode' (heap-const n _ _) (Data.List.Any.there e) = safeHeapCode' n e
safeHeapCode' (heap-const-code n _ _) (Data.List.Any.there e) = safeHeapCode' n e

safeHeapCode : ∀ {ht} {mem} {disas} {rt} {pc}
             → TypedHeap mem disas ht
             → (hl-const pc , τ-code rt) ∈ ht
             → SafeHeapCode disas pc ht rt
safeHeapCode (partial-done n) e = safeHeapCode' n e

data SafeProcess : Process → Set where
  typed-halted : ∀ {p}
               → Halted p
               → SafeProcess p
  typed-machine : ∀ {p} {registerTypes} {heapType}
                → Live p
                → TypedHeap (Process.memory p) (Process.disassembly p) heapType
                → TypedRegisters (Process.registers p) heapType (Process.disassembly p) registerTypes        
                → SafeCode (Process.insn p) (Process.fall p) heapType registerTypes
                → SafeProcess p
