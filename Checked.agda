open import System
open import Safety
open import Arch
open import Info
open ArchInfo info
open import μOps

open import Data.List using ([_]; []; _∷_; List)
open import Data.Product using (_,_; _×_; proj₁)
open import Data.BitVector using (zero)
open import Data.BitVector.Peano renaming (fromℕ to word; toℕ to projWord)
open import Data.Bool
import Data.Vec as Vec
open import Data.Vec using (Vec) renaming (_∷_ to _v∷_)
open import Disassembly using (Disassembly)
open import Data.Maybe
import Data.Fin as Fin

module Checked where
import Data.Nat as Nat
open import Relation.Binary
open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)
import Data.BitVector as BV
open import Relation.Binary.PropositionalEquality using (refl; subst)
reg-⊤ : ∀ {v : Word} {ht} {d} → TypedRegister v ht d τ-⊤
reg-⊤ {v} {ht} {d} =
  subst (λ v → TypedRegister v ht d τ-⊤)
        (mergeVecFullEq {lt = ≤-refl} {v = zeroWord} {v' = v})
        (reg-direct {v = v} {lt = ≤-refl} {b = zeroWord} ~⊤)

⊤-regs : ∀ {len} {disas} → (regs : Vec Word len) → (ht : HeapType) → TypedRegisters regs ht disas (Vec.replicate τ-⊤)
⊤-regs Vec.[] _ = regs-nil
⊤-regs (v Vec.∷ vs) ht = regs-cons reg-⊤ (⊤-regs vs ht)

-- Trivial halt check
module TrivialHalt where
  entryAddr : Word
  entryAddr = word 1

  haltEntry : (List μInsn × Word)
  haltEntry = [ halt ] , word 2

  disasm : Disassembly
  disasm index with projWord index
  ... | 1 = Maybe.just haltEntry
  ... | _ = Maybe.nothing

  process : Process
  process = record {
      registers = Vec.replicate (zero wordSize);
      flags = Vec.replicate (zero 1);
      pc = entryAddr;
      disassembly = disasm;
      memory = [];
      halted = false;
      fall = word 2;
      insn = [ halt ]
    }

  certificate : SafeProcess process
  certificate = typed-machine (λ x → x) (partial-done heap-nil) (⊤-regs (Process.registers process) []) safe-code-halt

-- Safe register operations, then a halt
module SimpleHalt where
  entryAddr : Word
  entryAddr = word 1

  halter : (List μInsn × Word)
  halter = move (reg Fin.zero (Fin.fromℕ 32)) (imm (word 0)) ∷
           halt ∷
           [] , word 2

  disasm : Disassembly
  disasm index with projWord index
  ... | 1 = Maybe.just halter
  ... | _ = Maybe.nothing

  process : Process
  process = record {
      registers = Vec.replicate (zero wordSize);
      flags = Vec.replicate (zero 1);
      pc = entryAddr;
      disassembly = disasm;
      memory = [];
      halted = false;
      fall = word 2;
      insn = proj₁ halter
    }

  certificate : SafeProcess process
  certificate = typed-machine (λ z → z) (partial-done heap-nil) (⊤-regs (Process.registers process) []) (safe-code-step (steptype-reg eτ-imm-num) safe-code-halt)

-- Fallthrough
module SimpleFall where
  entryAddr : Word
  entryAddr = word 1

  simpleOp : (List μInsn × Word)
  simpleOp = [ move (reg Fin.zero (Fin.fromℕ 32)) (imm (word 0)) ] , word 2

  halter : (List μInsn × Word)
  halter = [ halt ] , word 3

  disasm : Disassembly
  disasm index with projWord index
  ... | 1 = Maybe.just simpleOp
  ... | 2 = Maybe.just halter
  ... | _ = Maybe.nothing

  process : Process
  process = record {
      registers = Vec.replicate (zero wordSize);
      flags = Vec.replicate (zero 1);
      pc = entryAddr;
      disassembly = disasm;
      memory = [];
      halted = false;
      fall = word 2;
      insn = proj₁ simpleOp
    }

  heapType : HeapType
  heapType = (hl-const (word 1) , τ-code (Vec.replicate τ-⊤))
           ∷ (hl-const (word 2) , τ-code ((τ-num wordSize) v∷ (Vec.replicate τ-⊤)))
           ∷ []

  open import Data.List.Any using (here; there)

  heapTyping : TypedHeap [] disasm heapType
  heapTyping =
    partial-done (heap-const-code
                  (heap-const-code heap-nil (Disassembly.disas-known disasm refl) safe-code-halt)
                  (Disassembly.disas-known disasm refl) (safe-code-step (steptype-reg eτ-imm-num) (safe-code-fall (eτ-imm-ht (there (here refl))))))

  certificate : SafeProcess process
  certificate = typed-machine (λ z → z) heapTyping (⊤-regs (Process.registers process) heapType) (safe-code-step (steptype-reg eτ-imm-num) (safe-code-fall (eτ-imm-ht (there (here refl)))))
