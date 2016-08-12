module Safety.Progress where
open import System
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)

-- A value of type Steps p contains a successor for p, as well as a proof of
-- succession
Steps : Process → Set
Steps p₀ = Σ[ p₁ ∈ Process ] p₀ ↝ p₁

-- If an expression is well typed, and a process matches the context under which
-- the expression is well typed, then there is a concrete value it will evaluate
-- to.
exprProgress : ∀ {p : Process} {heapType} {registerTypes} {τ} {l}
                 {e : Expr (τ-bv l)}
             → TypedHeap (Process.memory p) (Process.disassembly p) heapType
             → TypedRegisters (Process.registers p) heapType
                              (Process.disassembly p) registerTypes
             → heapType , registerTypes ⊢ e ∶ τ
             → Σ[ v ∈ μVal (τ-bv l) ] p ⊢ e ⇝ v
exprProgress {e = imm i} _ _ eτ-imm-num    = val-bits i , eval-imm
exprProgress {e = imm i} _ _ (eτ-imm-ht _) = val-bits i , eval-imm

-- For every well typed process, that process is either in the halted state or
-- can step again
progress : {p : Process} → SafeProcess p → Steps p ⊎ Halted p
-- If the machine is safe due to being halted, then it is halted
progress (typed-halted halted) = inj₂ halted

-- If the machine's next operation is to halt, it transitions to a halted state
progress {p@record { insn = halt ∷ rest }} (typed-machine live _ _ _) =
  inj₁ (record p { halted = true; insn = rest } , ↝-μStep {p} live ↝-halt)

-- If we're moving a typed expression into a register, the exprProgress
-- lemma says that the expression can be evaluated, and so we have a successor
progress {p@record {insn = (move (reg r trunc) e ∷ rest)}}
         (typed-machine live typedHeap typedRegs
                        (safe-code-step (steptype-reg ht,rt⊢e∶τ) b)) =
  let v , p⊢e⇝v = exprProgress typedHeap typedRegs ht,rt⊢e∶τ in
  inj₁ (setReg (record p {insn = rest}) r trunc v ,
        ↝-μStep {p} live (↝-move-reg p⊢e⇝v))

-- Currently, memory and flag updates cannot be typed, and so we do not need
-- these cases.
progress {p@record {insn = (move (flag _) _ ∷ _)}}
         (typed-machine _ _ _ (safe-code-step () _))
progress {p@record {insn = (move mem _ ∷ _)}}
         (typed-machine _ _ _ (safe-code-step () _))

-- If we're done with the instruction, we fall through. This will always be
-- possible if there is a lifting of the fall address, and the typing
-- guarantees this.
progress {p} (typed-machine live typedHeap typedRegisters
                            (safe-code-fall (eτ-imm-ht fall∶τ-code))) =
  let shc = safeHeapCode typedHeap fall∶τ-code in
  inj₁ (record p {pc   = Process.fall p;
                  fall = SafeHeapCode.fall shc;
                  insn = SafeHeapCode.insn shc} ,
        ↝-fall live (proc-done {p}) (SafeHeapCode.dis-i shc))

-- Similarly to fallthrough, if we jump to a target, we can always make progress
-- as long as there is a lifting of the target address, which is gauranteed by
-- the typing.
progress {p} (typed-machine live typedHeap typedRegisters
                            (safe-code-jump (eτ-imm-ht {i = target}
                                                       target∶τ-code))) =
  let shc = safeHeapCode typedHeap target∶τ-code in
  inj₁ (record p {pc = target;
                  fall = SafeHeapCode.fall shc;
                  insn = SafeHeapCode.insn shc} ,
        ↝-jump {p = p} live (SafeHeapCode.dis-i shc) (↝-jmp eval-imm))

-- You can't type a jump with safe-code-step, because jmp will always escape the
-- instruction.
progress {p@record {insn = jmp _ ∷ _}}
         (typed-machine _ _ _ (safe-code-step () _))

-- Cond and cpu-exn are not yet typeable
progress {p@record {insn = cond _ _ _ ∷ _}}
         (typed-machine _ _ _ (safe-code-step () _))
progress {p@record {insn = cpu-exn _ ∷ _}}
         (typed-machine _ _ _ (safe-code-step () _))
