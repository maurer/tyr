open import Data.Sum
open import Data.Product
open import Data.Bool using (true)
open import Data.Unit using (tt)
open import Data.List using ([]; [_]; _∷_)
open import Relation.Binary.PropositionalEquality
open import Arch using (ArchInfo)
open import Info
open import Data.Maybe

module Safety where

open import System
open import μOps
open import Disassembly
-- A value of type Steps p contains a successor for p, as well as a proof of succession
Steps : Process → Set
Steps p₀ = Σ Process (λ p₁ → p₀ ↝ p₁)

exprProgress : ∀ {p : Process} {heapType} {registerTypes} {τ} {l} {e : Expr (τ-bv l)}
             → TypedHeap (Process.memory p) heapType
             → TypedRegisters (Process.registers p) heapType registerTypes
             → heapType , registerTypes ⊢ e ∶ τ
             → Σ (μVal (τ-bv l)) (λ v → p ⊢ e ⇝ v)
exprProgress {l = l} {e = imm {.l} i} _ _ eτ-imm-num = (val-bits i) , eval-imm

-- For every well typed process, that process is either in the halted state or can step again
progress : {p : Process} → SafeProcess p → Steps p ⊎ Halted p
-- If the machine is safe due to being halted, then it is halted
progress (typed-halted halted) = inj₂ halted
progress {p@record { insn = halt ∷ rest }} (typed-machine live x₁ x₂ safe-code-halt) =
  inj₁ (record p { halted = true; insn = rest } , ↝-μStep {p} live ↝-halt)

progress {p@record {insn = (move (reg r trunc) e ∷ rest)}} (typed-machine live ht rt (safe-code-step (steptype-reg et) b)) =
  let (v , j) = exprProgress ht rt et in
  inj₁ (setReg (record p {insn = rest}) r trunc v , ↝-μStep {p} live (↝-move-reg j))

-- If we execute an instruction which just modifies data, the new types correspond to the new process
typeStep : ∀ {p₀ p₁ : Process} {ht₀ ht₁} {rt₀ rt₁} {insn}
         → p₀ ↝⟨ insn ⟩ p₁ # Maybe.nothing
         → TypedHeap (Process.memory p₀) ht₀
         → TypedRegisters (Process.registers p₀) ht₀ rt₀
         → ⟨ ht₀ , rt₀ ⟩⇉⟨ insn ⟩⟨ ht₁ , rt₁ ⟩
         → (TypedHeap (Process.memory p₁) ht₁ × TypedRegisters (Process.registers p₁) ht₁ rt₁)
typeStep {ht₀ = ht₀} {ht₁ = .ht₀} {insn = move (reg n _) (imm i)} (↝-move-reg _) th tr (steptype-reg eτ-imm-num) = th , trUpdate tr reg-num n

-- If we execute an instruction which just modifies data, the new process is still live
typeStepLive : ∀ {p₀ p₁ : Process} {ht₀ ht₁} {rt₀ rt₁} {insn}
             → Live p₀
             → p₀ ↝⟨ insn ⟩ p₁ # Maybe.nothing
             → ⟨ ht₀ , rt₀ ⟩⇉⟨ insn ⟩⟨ ht₁ , rt₁ ⟩
             → Live p₁
typeStepLive live (↝-move-reg _) (steptype-reg eτ-imm-num) = live

-- For every well typed process, taking a step results in a new well typed process
preservation : {p₀ p₁ : Process} → SafeProcess p₀ → p₀ ↝ p₁ → SafeProcess p₁
-- If the process is safe because it has stopped, no step exists
preservation (typed-halted halted) step with (live-step step) halted
... | ()
-- If the next instruction is halt, it must proceed via μStep, not fall or jump
preservation {record {insn = .(halt ∷ _)}} (typed-machine _ _ _ safe-code-halt) (↝-fall _ () _)
preservation {record {insn = .(halt ∷ _)}} (typed-machine _ _ _ safe-code-halt) (↝-jump _ _ ())
-- If the next instruction is halt, the machine becomes halted, and is safe for that reason
preservation {p@record {insn = .(halt ∷ _)}} (typed-machine _ _ _ safe-code-halt) (↝-μStep _ ↝-halt) = typed-halted tt

-- If the next instruction is safe as a typed data transition, no fallthrough or jumping actions are being taken
preservation (typed-machine _ _ _ (safe-code-step _ _)) (↝-fall _ () _)
preservation (typed-machine _ _ _ (safe-code-step () _)) (↝-jump _ _ (↝-jmp _))

preservation {p₀ = p₀@record {insn = insn ∷ insns; fall = fall}} {p₁ = record {insn = .insns; fall = .fall}} (typed-machine live ht rt (safe-code-step typeProp safeNext)) step@(↝-μStep _ μStep) =
  let (ht' , rt') = typeStep μStep ht rt typeProp
  in typed-machine (typeStepLive live μStep typeProp) ht' rt' safeNext

-- If the process p₀ is well typed, and it can evolve to some future process p, then the future process has halted or can take a step.
safety : {p₀ p : Process} → SafeProcess p₀ → p₀ ↝* p → Steps p ⊎ Halted p
safety typing trans = progress (↝*-transport preservation typing trans)
