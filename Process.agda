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
open import Value

module Process (info : ArchInfo) where

Word = BitVector (ArchInfo.wordSize info)
Flag = BitVector 1

open import Disassembly info using (Disassembly)

record Process : Set where
  field
    registers : Vec Word  (ArchInfo.numRegs info)
    flags : Vec Flag (ArchInfo.numFlags info)
    pc : Word
    disassembly : Disassembly
    memory : Memory (ArchInfo.wordSize info)
    halted : Bool

Halted : Process → Set
Halted p = T (Process.halted p)

Live : Process → Set
Live p = ¬ (Halted p)
