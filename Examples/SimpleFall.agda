-- This tests our ability to describe instruction fallthrough without
-- manually concatenating the instructions. This is also the simplest
-- example that mandates the use of code pointer typing.
module Examples.SimpleFall where

open import Examples.Util

entryAddr : Word
entryAddr = word 1

simpleOp : DisassemblyEntry 
simpleOp = [ move r0 (# (+ 0)) ] , word 2

halter : DisassemblyEntry
halter = [ halt ] , word 3

disasm : Disassembly
disasm index with projWord index
... | 1 = just simpleOp
... | 2 = just halter
... | _ = nothing

process : Process
process = record {
    registers = replicate (zero wordSize);
    flags = replicate (zero 1);
    pc = entryAddr;
    disassembly = disasm;
    memory = [];
    halted = false;
    fall = word 2;
    insn = proj₁ simpleOp
  }

halter-in : RegisterTypes
halter-in = (replicate τ-⊤) [ rid0 ]≔ τ-num wordSize

heapType : HeapType
heapType = (hl-const (word 1) , τ-code (replicate τ-⊤))
         ∷ (hl-const (word 2) , τ-code halter-in)
         ∷ []

halter-τ : SafeCode (proj₁ halter) (word 3) heapType halter-in
halter-τ = safe-code-halt

simple-τ : SafeCode (proj₁ simpleOp) (word 2) heapType (replicate τ-⊤)
simple-τ = safe-code-step (steptype-reg eτ-imm-num)
                          (safe-code-fall (eτ-imm-ht (there (here refl)))) 

heapTyping : TypedHeap [] disasm heapType
heapTyping =
  partial-done
  (heap-const-code
  (heap-const-code heap-nil
    (disas-known refl) halter-τ)
    (disas-known refl) simple-τ)

certificate : SafeProcess process
certificate = typed-machine (λ z → z)
                            heapTyping
                            (⊤-regs (Process.registers process) heapType)
                            simple-τ
