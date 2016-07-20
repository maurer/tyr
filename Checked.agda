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
open import Data.Vec using (Vec)
open import Disassembly using (Disassembly)
open import Data.Maybe
import Data.Fin as Fin

module Checked where

⊤-regs : ∀ {len} → (regs : Vec Word len) → (ht : HeapType) → TypedRegisters regs ht (Vec.replicate τ-⊤)
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
  certificate = typed-machine (λ x → x) heap-nil (⊤-regs (Process.registers process) ht-none) safe-code-halt

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
  certificate = typed-machine (λ z → z) heap-nil (⊤-regs (Process.registers process) ht-none) (safe-code-step (steptype-reg eτ-imm-num) safe-code-halt)

