open import Arch using (ArchInfo)
open import Info
module Typing where

open import Process using (Process; Halted; Live)
open import μOps

open import Data.Bool using (Bool; T)
open import Data.Vec using (Vec)
open import Data.List using ([_]; _∷_)
open import Data.Unit using (⊤)
open import Memory
open import Disassembly
open import Data.Maybe

data HeapType : Set where

data RegisterTypes : Set where

data TypedRegisters : Vec Word (ArchInfo.numRegs info) → HeapType → RegisterTypes → Set where

data TypedHeap : Memory → HeapType → Set where

data SafeCode : Sema → Word → HeapType → RegisterTypes → Set where
  safe-code-halt : ∀ {fall} {insns} {ht} {rt} → SafeCode (halt ∷ insns) fall ht rt

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

data Kind : Set where

data Type : Set where
  ⟨⟩ : Type
