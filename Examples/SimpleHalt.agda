-- Zeroes r0 before halting. This tests our ability to deal with sequenced
-- μInsns.
module Examples.SimpleHalt where

open import Examples.Util

entryAddr : Word
entryAddr = word 1

halter : DisassemblyEntry
halter = move r0 (# (+ 0)) ∷
         halt ∷
         [] , word 2

disasm : Disassembly
disasm index with projWord index
... | 1 = just halter
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
    insn = proj₁ halter
  }

certificate : SafeProcess process
certificate = typed-machine (λ z → z)
                            (partial-done heap-nil)
                            (⊤-regs (Process.registers process) [])
                            (safe-code-step (steptype-reg eτ-imm-num)
                                            safe-code-halt)
