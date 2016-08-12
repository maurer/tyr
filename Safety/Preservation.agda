module Safety.Preservation where

open import System

open import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_; prop-toℕ-≤)
open import Data.Nat as Nat using (suc; ℕ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (subst; sym; _≡_; refl;
                                                         cong)
import Data.Maybe as Maybe
open import Data.Product using (_×_; _,_)
import Data.Vec as Vec
open import Data.List using (_∷_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)

open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)

-- Convenience alias for the size of a full width GPR
wordFin : Fin (suc wordSize)
wordFin = Fin.fromℕ wordSize

-- Lemma indicating that if a value looks up something in the disassembly,
-- then merging it with anything else also looks up the same thing since
-- addresses must be full width.
disasMerge : ∀ {d} {r v} {i} {f}
           → d ⟦ v ↦⟨ i , f ⟩⟧
           → d ⟦ mergeVec {lt = ≤-refl} r v ↦⟨ i , f ⟩⟧
disasMerge {d} {r} {v} {i} {f} disas =
  subst (λ v → d ⟦ v ↦⟨ i , f ⟩⟧)
        (sym (mergeVecFullEq {lt = ≤-refl} {v = r} {v' = v}))
        disas

-- Lemma stating that the size of any pointer typed expression is one word
ptrSize : ∀ {n : ℕ} {ht} {rt} {e : Expr (τ-bv n)} {τ}
        → ht , rt ⊢ e ∶ (τ-ptr τ)
        → wordSize ≡ n
ptrSize {n} ep with wordSize Nat.≟ n 
... | yes p = p
ptrSize (eτ-imm-ht x) | no _ = refl

-- Lemma to strip off the successors in a natural number equality
≡-pred : ∀ {m} {n}
       → Nat.suc m ≡ Nat.suc n
       → m ≡ n
≡-pred refl = refl

-- We can move toℕ across ≡ into fromℕ, since with m and n equal,
-- fromℕ and toℕ become inverses.
fin-≡-commute : ∀ {m : ℕ} {n : Fin (Nat.suc m)}
              → m ≡ Fin.toℕ n
              → Fin.fromℕ m ≡ n
fin-≡-commute {0} {Fin.zero} _ = refl
fin-≡-commute {0} {Fin.suc _} ()
fin-≡-commute {Nat.suc m} {Fin.zero} ()
fin-≡-commute {Nat.suc m} {Fin.suc n} p =
  cong Fin.suc (fin-≡-commute (≡-pred p))

-- A Fin (Nat.suc wordSize) version of ptrSize, for use with reference to GPRs
finPtrSize : ∀ {n} {ht} {rt} {e : Expr (τ-bv (Fin.toℕ n))} {τ}
           → ht , rt ⊢ e ∶ (τ-ptr τ)
           → wordFin ≡ n
finPtrSize e∶ptr = fin-≡-commute (ptrSize e∶ptr)

-- If we execute a typed instruction on a process that matches its input types,
-- the resulting process will match its output types
typeStep : ∀ {p₀ p₁ : Process} {ht₀ ht₁} {rt₀ rt₁} {insn}
         → p₀ ↝⟨ insn ⟩ p₁ # Maybe.nothing
         → TypedHeap (Process.memory p₀) (Process.disassembly p₀) ht₀
         → TypedRegisters (Process.registers p₀) ht₀
                          (Process.disassembly p₀) rt₀
         → ⟨ ht₀ , rt₀ ⟩⇉⟨ insn ⟩⟨ ht₁ , rt₁ ⟩
         → (TypedHeap (Process.memory p₁) (Process.disassembly p₁) ht₁ ×
            TypedRegisters (Process.registers p₁) ht₁
                           (Process.disassembly p₁) rt₁)
-- Values of type ⊤ cannot be used for anything, so we cannot possibly type this
typeStep _ _ _ (steptype-reg {τ = τ-⊤} ())

-- Raw code values are not currently constructable, only code pointers
typeStep _ _ _ (steptype-reg {τ = τ-code x} ())

-- If we are moving a number into a register, the proof that the new register is
-- a legal number is trivial
typeStep (↝-move-reg {n = n} {r = r} _)
         typedHeap typedRegisters
         (steptype-reg {τ = τ-num _} eτ-imm-num) =
         typedHeap , trUpdate typedRegisters
                              (reg-direct {lt = prop-toℕ-≤ n} ~num)
                              r

-- Currently, the only way to construct a pointer is by its presence in the
-- initial heap, so we can just propogate that proof to the new register.
typeStep {p₀}
         (↝-move-reg {n = n} {r} e⇝v)
         typedHeap typedRegisters
         (steptype-reg {τ = τ-ptr τ} e∶ptr-τ)
         with e⇝v | e∶ptr-τ | finPtrSize e∶ptr-τ
... | eval-imm | eτ-imm-ht a∈heapType | refl =
  typedHeap ,
  trUpdate typedRegisters
           (reg-direct {lt = ≤-refl}
                       {b = Vec.lookup r (Process.registers p₀)}
                       (~ptr a∈heapType))
           r

-- μInsns which update typing do not change liveness of the process
typeStepLive : ∀ {p₀ p₁ : Process} {ht₀ ht₁} {rt₀ rt₁} {insn}
             → Live p₀
             → p₀ ↝⟨ insn ⟩ p₁ # Maybe.nothing
             → ⟨ ht₀ , rt₀ ⟩⇉⟨ insn ⟩⟨ ht₁ , rt₁ ⟩
             → Live p₁
typeStepLive _ ↝-halt ()
typeStepLive _ (↝-move-mem _) ()
typeStepLive _ (↝-move-flag _) ()
typeStepLive live (↝-move-reg _) (steptype-reg _) = live

-- For every well typed process, taking a step results in a new well typed process
preservation : {p₀ p₁ : Process} → SafeProcess p₀ → p₀ ↝ p₁ → SafeProcess p₁
-- If the process is safe because it has stopped, no step exists
preservation (typed-halted halted) step with (live-step step) halted
... | ()

-- If the next instruction is halt, it must proceed via μStep, not fall or jump
preservation {record {insn = .(halt ∷ _)}} (typed-machine _ _ _ safe-code-halt)
                                           (↝-fall _ () _)
preservation {record {insn = .(halt ∷ _)}} (typed-machine _ _ _ safe-code-halt)
                                           (↝-jump _ _ ())

-- If the next instruction is halt, the machine becomes halted (and so safe)
preservation {p@record {insn = .(halt ∷ _)}}
             (typed-machine _ _ _ safe-code-halt)
             (↝-μStep _ ↝-halt) = typed-halted tt

-- If the next instruction is safe as a typed data transition, no fallthrough or
-- jumping actions are being taken
preservation (typed-machine _ _ _ (safe-code-step _ _)) (↝-fall _ () _)
preservation (typed-machine _ _ _ (safe-code-step () _)) (↝-jump _ _ (↝-jmp _))

-- If the next step is typed as a data transition, applying the data transition
-- gives a typed successory by typeStep.
preservation (typed-machine live typedHeap typedRegisters
                            (safe-code-step typeProp safeNext))
             step@(↝-μStep _ μStep) =
  let (typedHeap′ , typedRegisters′) =
        typeStep μStep typedHeap typedRegisters typeProp
  in typed-machine (typeStepLive live μStep typeProp) typedHeap′ typedRegisters′
                   safeNext

-- If we fall through, the only thing that changes is the safety proof for the
-- currently loaded instruction.
preservation (typed-machine _ typedHeap typedRegisters
                            (safe-code-fall (eτ-imm-ht a∈heapType)))
             (↝-fall live _ d)
             with safeHeapCode typedHeap a∈heapType
... | shc with unique-disas d (SafeHeapCode.d⟦pc↦⟨sema,fall⟩⟧ shc)
... | refl , refl = typed-machine live typedHeap typedRegisters
                                  (SafeHeapCode.safe shc)

-- If we jump, we do the same thing as falling through, but for the target
-- address rather than the fallthrough one.
preservation {record { insn = (jmp (imm i) ∷ _) }}
             (typed-machine _ typedHeap typedRegisters
                            (safe-code-jump (eτ-imm-ht a∈heapType)))
             (↝-jump {pc' = pc′} live d q)
             with safeHeapCode typedHeap a∈heapType
                | jmp-to-target {i = i} {pc' = pc′} q
... | shc | refl , refl with unique-disas d (SafeHeapCode.d⟦pc↦⟨sema,fall⟩⟧ shc)
... | refl , refl = typed-machine live typedHeap typedRegisters
                                  (SafeHeapCode.safe shc)

-- Jumps cannot be performed by a μStep or a fallthrough
preservation (typed-machine _ _ _ (safe-code-jump (eτ-imm-ht _)))
             (↝-μStep _ ())
preservation (typed-machine _ _ _ (safe-code-jump (eτ-imm-ht _)))
             (↝-fall  _ () _)
