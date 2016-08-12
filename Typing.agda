-- This module defines the certificate over a program that the saftey theorem
-- will show gaurantees our saftey policy.
module Typing where

open import Info
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
open import Data.List.Any using (here; there)

data Type : Set
RegisterTypes = Vec Type numRegs

data Type where
  -- Any value can be of type ⊤
  τ-⊤ : Type
  -- Any value of the right bit length can be of type num
  τ-num : ℕ → Type
  -- Jumping to a pointer to this value is legal as long as registers are a
  -- subtype of selected RegisterTypes (e.g. the data form is an instruction)
  τ-code : RegisterTypes → Type
  -- This value is an address which can be read/written as the enclosed type
  τ-ptr : Type → Type

data HeapLoc : Set where
  -- Constant address, as for ro code segment or a global
  hl-const : Word → HeapLoc

HeapEntry = HeapLoc × Type
-- A HeapType describes a pairing of locations and types that a memory should
-- have to match the heap typing
HeapType = List HeapEntry

open Data.List.Any.Membership (peSetoid HeapEntry) using (_∈_)

-- A typed register is a proof that a register value is a bitwise extension
-- of a legal representation of a type.
data TypedRegister : Word → HeapType → Disassembly → Type → Set
-- TypedRegisters is a proof that an entire set of registers has a type
-- assignment under the same heap type.
data TypedRegisters : ∀ {len} → Vec Word len → HeapType → Disassembly
                    → Vec Type len → Set
-- heapType ⊢ w ~ τ means that the concrete value w is a
-- representative of type τ in the presence of heapType
data _⊢_~_ : ∀ {l} → HeapType → BitVector l → Type → Set
-- heapType , registerTypes ⊢ e ∶ τ means that the expression e has type τ under
-- the heap and register types on the left
data _,_⊢_∶_ : ∀ {l} → HeapType → RegisterTypes → Expr (τ-bv l) → Type → Set
-- ⟨ heapType₀ , registerTypes₀ ⟩⇉⟨ i ⟩⟨ heapType₁ , registerTypes₁ ⟩
-- means that executing the instruction i on a process with heap type and
-- register types as on the left will produce a process with heap type and
-- register type as on the right
data ⟨_,_⟩⇉⟨_⟩⟨_,_⟩ : HeapType → RegisterTypes → μInsn
                    → HeapType → RegisterTypes → Set
-- SafeCode indicates that a given sequence of μInsn, with a provided
-- fallthrough, will keep executing until it halts if run in a process
-- that matches the HeapType and RegisterTypes.
data SafeCode : Sema → Word → HeapType → RegisterTypes → Set

data _⊢_~_ where
  ~⊤ : ∀ {l} {v : BitVector l} {ht}
     → ht ⊢ v ~ τ-⊤
  ~num : ∀ {l} {v : BitVector l} {ht}
       → ht ⊢ v ~ τ-num l
  ~ptr : ∀ {v : Word} {ht} {τ}
       → (hl-const v , τ) ∈ ht
       → ht ⊢ v ~ τ-ptr τ

data TypedRegister where
  reg-direct : ∀ {l} {v : BitVector l} {lt} {ht} {d} {τ} {b}
             → ht ⊢ v ~ τ 
             → TypedRegister (mergeVec {lt = lt} b v) ht d τ
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
  safe-code-halt : ∀ {fall} {insns} {ht} {rt}
                 → SafeCode (halt ∷ insns) fall ht rt
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

-- trUpdate is a convenience function which swaps out a TypedRegister used in
-- a complete TypedRegisters record with the new one provided.
trUpdate : ∀ {len} {regs} {ht} {rt} {rts} {v} {d}
         → TypedRegisters {len} regs ht d rts
         → TypedRegister v ht d rt
         → (i : Fin len)
         → TypedRegisters {len} (regs [ i ]≔ v) ht d (rts [ i ]≔ rt)
trUpdate {0} _ _ ()
trUpdate (regs-cons rt₀ rts) rt₁ Fin.zero = regs-cons rt₁ rts
trUpdate (regs-cons rt₀ rts) rt₁ (Fin.suc i) =
  regs-cons rt₀ (trUpdate rts rt₁ i)


-- PartialTypedHeap is a mid-construction type for creating a proof that a
-- memory value corresponds to a HeapType.
-- PartialTypedHeap mem disas heapType heapType₀ means that if you assume
-- heapType matches (as you would when typechecking a recursive function)
-- recursive typechecking algorithm), you can derive that heapType₀ matches.
-- The constructors prepend to ht₀ as it is built up. 
data PartialTypedHeap : Memory → Disassembly → HeapType → HeapType → Set where
  heap-nil   : ∀ {mem} {disas} {ht} → PartialTypedHeap mem disas ht []
  -- FUTURE: heap-const and heap-const-code could be merged
  -- Specifically, if we can treat code as first-class rather than something
  -- that will only ever be pointed at, ht ⊢ v ~ τ-code rt would be possible
  heap-const : ∀ {mem} {disas} {ht} {ht₀} {k} {l} {v} {τ}
             → PartialTypedHeap mem disas ht ht₀
             → Read mem k l v
             → ht ⊢ v ~ τ
             → PartialTypedHeap mem disas ht (((hl-const k) , τ) ∷ ht₀)
  heap-const-code : ∀ {mem} {disas} {ht} {ht₀} {k} {insns} {fall} {rt}
                  → PartialTypedHeap mem disas ht ht₀
                  → disas ⟦ k ↦⟨ insns , fall ⟩⟧
                  → SafeCode insns fall ht rt
                  → PartialTypedHeap mem disas ht
                                     (((hl-const k) , τ-code rt) ∷ ht₀)

-- TypedHeap is a proof that a memory object corresponds to a HeapType.
-- This is done by using a PartialTypedHeap whose assumptions and conclusions
-- are identical, thus satisfying the mutual recursion obligations.
data TypedHeap : Memory → Disassembly → HeapType → Set where
  partial-done : ∀ {mem} {disas} {ht}
               → PartialTypedHeap mem disas ht ht
               → TypedHeap mem disas ht

-- SafeHeapCode is a convenience lookup record for extracting the reason why a
-- target address is safe.
record SafeHeapCode (disas : Disassembly)
                    (pc : Word)
                    (ht : HeapType)
                    (rt : RegisterTypes) : Set where
  field
    fall              : Word
    sema              : List μInsn
    safe              : SafeCode sema fall ht rt
    d⟦pc↦⟨sema,fall⟩⟧ : disas ⟦ pc ↦⟨ sema , fall ⟩⟧

-- safeHeapCode′ is the raw recursive function that walks the PartialTypedHeap
-- to extract a SafeHeapCode record which must exist, given its presence in the
-- HeapType
safeHeapCode′ : ∀ {ht₀} {ht} {mem} {disas} {rt} {pc}
              → PartialTypedHeap mem disas ht₀ ht
              → (hl-const pc , τ-code rt) ∈ ht
              → SafeHeapCode disas pc ht₀ rt
-- If this entry is the one for the code pointer, heap-const is impossible. 
safeHeapCode′ (heap-const _ _ ~⊤)       (Data.List.Any.here ())
safeHeapCode′ (heap-const _ _ ~num)     (Data.List.Any.here ())
safeHeapCode′ (heap-const _ _ (~ptr _)) (Data.List.Any.here ())
-- If we're at the index, export the information from heap-const-code 
safeHeapCode′ (heap-const-code {insns = sema} {fall = fall} _ d s) (here refl) =
                record { fall = fall ;
                         sema = sema;
                         safe = s ;
                         d⟦pc↦⟨sema,fall⟩⟧ = d }
-- Otherwise, recurse
safeHeapCode′ (heap-const pth _ _) (there i) = safeHeapCode′ pth i
safeHeapCode′ (heap-const-code pth _ _) (there i) = safeHeapCode′ pth i

-- safeHeapCode wraps safeHeapCode′ to extract SafeHeapCode information for any
-- entry in the heapType which the TypedHeap demonstrates the memory matches.
safeHeapCode : ∀ {ht} {mem} {disas} {rt} {pc}
             → TypedHeap mem disas ht
             → (hl-const pc , τ-code rt) ∈ ht
             → SafeHeapCode disas pc ht rt
safeHeapCode (partial-done pth) i = safeHeapCode′ pth i

-- SafeProcess is the predicate intended to mean that the process it is over
-- will be safe. It is this predicate over which the saftey theorem is proved.
data SafeProcess : Process → Set where
  -- If it is halted, it is trivially safe, as it will do nothing.
  typed-halted : ∀ {p}
               → Halted p
               → SafeProcess p
  -- If the machine is live, and there is a correspondence between its heap,
  -- and a heapType, its registers and registerTypes, and the code it is about
  -- to execute is safe under those types, then the whole machine is safe.
  typed-machine : ∀ {p} {registerTypes} {heapType}
                → Live p
                → TypedHeap (Process.memory p) (Process.disassembly p) heapType
                → TypedRegisters (Process.registers p) heapType
                                 (Process.disassembly p) registerTypes        
                → SafeCode (Process.insn p) (Process.fall p)
                           heapType registerTypes
                → SafeProcess p
