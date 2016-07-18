open import Data.Vec using (Vec)
open import Data.BitVector using (BitVector; Bit)
open import Memory using (Memory)
open import Arch using (ArchInfo)
open import Data.Bool using (Bool; T; not)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_)
open import Relation.Nullary using (¬_)
open import Data.List using (List)
open import Relation.Binary using (StrictTotalOrder)
open import μOps
open import Value

module Process where
open import Info

Word = BitVector (ArchInfo.wordSize info)
Flag = BitVector 1

open import Disassembly using (Disassembly)

record Process : Set where
  field
    registers : Vec Word  (ArchInfo.numRegs info)
    flags : Vec Flag (ArchInfo.numFlags info)
    pc : Word
    fall : Word
    insn : List μInsn
    disassembly : Disassembly
    memory : Memory
    halted : Bool

Halted : Process → Set
Halted p = T (Process.halted p)

Live : Process → Set
Live p = ¬ (Halted p)
