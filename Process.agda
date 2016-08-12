-- This module has the representation for a concrete Process, e.g. a complete
-- program state, sufficient to determine its entire evolution.
open import Data.Vec using (Vec)
open import Data.BitVector using (BitVector)
open import Memory using (Memory)
open import Data.Bool using (Bool; T)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (¬_)
open import Data.List using (List)
open import Disassembly using (Disassembly; _⟦_↦⟨_,_⟩⟧)
open import μOps using (μInsn)

open import Info

-- Shorthand for a flag value
Flag = BitVector 1

-- Record describing a program state (possibly intermediate)
record Process : Set where
  field
    -- Current GPR values
    registers : Vec Word numRegs
    -- Current flag register values
    flags : Vec Flag numFlags
    -- The pc which is currently being executed
    pc : Word
    -- The address to go to once the μInsns in insn are exhausted
    fall : Word
    -- The remaining μInsns to perform to complete this instruction
    insn : List μInsn
    -- Known semantics for some addresses
    disassembly : Disassembly
    -- Current contents of RAM
    memory : Memory
    -- Whether or not we are halted
    halted : Bool

-- Halted field reified into a predicate
Halted : Process → Set
Halted p = T (Process.halted p)

-- Liveness is defined as the negation of being halted
Live : Process → Set
Live p = ¬ (Halted p)
