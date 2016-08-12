-- This is the simplest possible program to check (which is not already halted):
-- it immediately halts.

module Examples.TrivialHalt where

open import Examples.Util

entryAddr : Word
entryAddr = word 1

haltEntry : DisassemblyEntry
haltEntry = [ halt ] , word 2

disasm : Disassembly
disasm index with projWord index
... | 1 = just haltEntry
... | _ = nothing

process : Process
process = record {
    registers = replicate zeroWord;
    flags = replicate falseFlag;
    pc = entryAddr;
    disassembly = disasm;
    memory = [];
    halted = false;
    fall = word 2;
    insn = [ halt ]
  }

certificate : SafeProcess process
certificate =
  typed-machine (λ x → x)
                (partial-done heap-nil)
                (⊤-regs (Process.registers process) [])
                safe-code-halt
