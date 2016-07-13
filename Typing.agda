open import Arch using (ArchInfo)

module Typing (info : ArchInfo) where

open import Process info using (Process; Halted; Live)
open import μOps info

open import Data.Bool using (Bool; T)
open import Data.Vec using (Vec)
open import Data.List using ([_])
open import Data.Unit using (⊤)
open import Memory (ArchInfo.wordSize info)
open import Disassembly info
open import Data.Maybe

data HeapType : Set where

data RegisterTypes : Set where

data TypedRegisters : Vec Word (ArchInfo.numRegs info) → HeapType → RegisterTypes → Set where

data TypedHeap : Memory → HeapType → Set where

data SafeCode : Sema → Word → HeapType → RegisterTypes → Set where
  safe-code-halt : ∀ {fall} {ht} {rt} → SafeCode ([ halt ]) fall ht rt

data SafeProcess : Process → Set where
  typed-halted : ∀ {p}
               → Halted p
               → SafeProcess p
  typed-machine : ∀ {p} {registerTypes} {heapType} {sema} {fall}
                → Live p
                → TypedHeap (Process.memory p) heapType
                → TypedRegisters (Process.registers p) heapType registerTypes
                → (Process.disassembly p) ⟦ Process.pc p ↦⟨ sema , fall ⟩⟧
                → SafeCode sema fall heapType registerTypes
                → SafeProcess p

data Kind : Set where

data Type : Set where
  ⟨⟩ : Type
