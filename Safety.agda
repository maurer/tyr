open import Data.Sum
open import Data.Product
open import Data.Bool using (true)
open import Data.Unit using (tt)
open import Data.List using ([]; [_]; _∷_)
import Data.List.Any
open import Relation.Binary.PropositionalEquality
open import Arch using (ArchInfo)
open import Info
open import Data.Maybe
import Data.Fin
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; suc) renaming (decTotalOrder to ℕdecTotalOrder)
open import Relation.Binary
open import Data.Bool using (Bool)
import Data.Vec as Vec
open import Data.Empty

module Safety where

open import System
open import μOps
open import Disassembly
open ArchInfo info
import Data.BitVector
zeroWord : System.Word
zeroWord = Data.BitVector.zero wordSize

-- A value of type Steps p contains a successor for p, as well as a proof of succession
Steps : Process → Set
Steps p₀ = Σ Process (λ p₁ → p₀ ↝ p₁)

exprProgress : ∀ {p : Process} {heapType} {registerTypes} {τ} {l} {e : Expr (τ-bv l)}
             → TypedHeap (Process.memory p) (Process.disassembly p) heapType
             → TypedRegisters (Process.registers p) heapType (Process.disassembly p) registerTypes
             → heapType , registerTypes ⊢ e ∶ τ
             → Σ (μVal (τ-bv l)) (λ v → p ⊢ e ⇝ v)
exprProgress {l = l} {e = imm {.l} i} _ _ eτ-imm-num = (val-bits i) , eval-imm
exprProgress {l = .wordSize} {e = imm {.wordSize} i} _ _ (eτ-imm-ht p) = (val-bits i) , eval-imm

-- For every well typed process, that process is either in the halted state or can step again
progress : {p : Process} → SafeProcess p → Steps p ⊎ Halted p
-- If the machine is safe due to being halted, then it is halted
progress (typed-halted halted) = inj₂ halted
progress {p@record { insn = halt ∷ rest }} (typed-machine live _ _ _) = inj₁
  (record p { halted = true; insn = rest } , ↝-μStep {p} live ↝-halt)

progress {p@record {insn = (move (reg r trunc) e ∷ rest)}} (typed-machine live ht rt (safe-code-step (steptype-reg et) b)) =
  let (v , j) = exprProgress ht rt et in
  inj₁ (setReg (record p {insn = rest}) r trunc v , ↝-μStep {p} live (↝-move-reg j))
progress {p@record {insn = (move (flag f) e ∷ rest)}} (typed-machine live ht rt (safe-code-step () _))
progress {p@record {insn = (move mem e ∷ rest)}} (typed-machine live ht rt (safe-code-step () _))
 
progress {p@record { registers = registers ; flags = flags ; pc = pc ; fall = fall ; insn = .[] ; disassembly = disassembly ; memory = memory ; halted = halted }} (typed-machine live ht rt (safe-code-fall (eτ-imm-ht c))) =
  let record {fall = fall'; insn = insn; dis-i = disas} = safeHeapCode ht c in
  inj₁ (record p {pc = fall; fall = fall'; insn = insn} , ↝-fall live (proc-done {p}) disas)
progress {p@record {insn = jmp e ∷ rest}} (typed-machine live ht rt (safe-code-jump (eτ-imm-ht {i = i} c))) =
  let record {fall = fall'; insn = insn; dis-i = disas} = safeHeapCode ht c in
  inj₁ (record p {pc = i; fall = fall'; insn = insn} , ↝-jump {p = p} live disas (↝-jmp eval-imm))

progress {p@record {insn = jmp _ ∷ _}} (typed-machine _ _ _ (safe-code-step () _))
progress {p@record {insn = cond _ _ _ ∷ _}} (typed-machine _ _ _ (safe-code-step () _))
progress {p@record {insn = cpu-exn _ ∷ _}} (typed-machine _ _ _ (safe-code-step () _))



wordFin : Fin (suc wordSize)
wordFin = Data.Fin.fromℕ wordSize
open import Relation.Nullary using (yes; no)

open DecTotalOrder ℕdecTotalOrder using () renaming (refl to ≤-refl)

disasMerge : ∀ {d} {r v} {i} {f}
           → d ⟦ v ↦⟨ i , f ⟩⟧
           → d ⟦ mergeVec {lt = ≤-refl} r v ↦⟨ i , f ⟩⟧
disasMerge {d} {r} {v} {i} {f} disas =
  subst (λ v → d ⟦ v ↦⟨ i , f ⟩⟧)
        (sym (mergeVecFullEq {lt = ≤-refl} {v = r} {v' = v}))
        disas

ef : ∀ {n : ℕ} {ht} {rt} {e : Expr (τ-bv n)} {τ}
   → ht , rt ⊢ e ∶ (τ-ptr τ)
   → wordSize ≡ n
ef {n} ep with wordSize Data.Nat.≟ n 
ef _ | yes p = p
ef {.32} (eτ-imm-ht x) | no ¬p = refl

hh : ∀ {n}
   → wordSize ≡ n
   → n Data.Nat.≤ wordSize
hh refl = ≤-refl

fg : ∀ {n : ℕ}
   → (p : wordSize ≡ n)
   → wordFin ≡ Data.Fin.fromℕ≤ {m = n} (Data.Nat.s≤s (hh p))
fg {.32} refl = refl

shift : ∀ {m} {n}
      → Data.Nat.suc m ≡ (Data.Nat.suc n)
      → m ≡ n
shift refl = refl

upgrade : ∀ {m : ℕ} {n : Fin (Data.Nat.suc m)}
        → m ≡ (Data.Fin.toℕ n)
        → Data.Fin.fromℕ m ≡ n
upgrade {0} {Data.Fin.zero} _ = refl
upgrade {0} {Data.Fin.suc _} ()
upgrade {Data.Nat.suc m} {Data.Fin.zero} ()
upgrade {Data.Nat.suc m} {Data.Fin.suc n} p = cong Data.Fin.suc (upgrade (shift p))

lemmer : ∀ {n} {ht} {rt} {e : Expr (τ-bv (Data.Fin.toℕ n))} {τ}
       → ht , rt ⊢ e ∶ (τ-ptr τ)
       → wordFin ≡ n
lemmer {n} qq =
  let q = ef qq
      bar = fg q
  in upgrade q
--cong (λ x → Data.Fin.fromℕ≤ (Data.Nat.s≤s (hh {!!}))) q

-- If we execute an instruction which just modifies data, the new types correspond to the new process
typeStep : ∀ {p₀ p₁ : Process} {ht₀ ht₁} {rt₀ rt₁} {insn}
         → p₀ ↝⟨ insn ⟩ p₁ # Maybe.nothing
         → TypedHeap (Process.memory p₀) (Process.disassembly p₀) ht₀
         → TypedRegisters (Process.registers p₀) ht₀ (Process.disassembly p₀) rt₀
         → ⟨ ht₀ , rt₀ ⟩⇉⟨ insn ⟩⟨ ht₁ , rt₁ ⟩
         → (TypedHeap (Process.memory p₁) (Process.disassembly p₁) ht₁ × TypedRegisters (Process.registers p₁) ht₁ (Process.disassembly p₁) rt₁)
--typeStep {ht₀ = ht₀} {ht₁ = .ht₀} {insn = move (reg n _) (imm i)} (↝-move-reg _) th tr (steptype-reg eτ-imm-num) = th , trUpdate tr reg-num n
--typeStep {ht₀ = ht₀} {ht₁ = .ht₀} {insn = move (reg n len) (imm i)} (↝-move-reg eval-imm) th tr (steptype-reg (_)) 
typeStep _ _ _ (steptype-reg {τ = τ-⊤} ())
typeStep {ht₀ = ht₀} {ht₁ = .ht₀} (↝-move-reg {n = n} {r = r} _) th tr (steptype-reg {τ = τ-num _} eτ-imm-num) =  th , trUpdate tr (reg-direct {lt = fin-lt n} ~num) r
typeStep a b c (steptype-reg {τ = τ-code x} ())
typeStep {p₀} {ht₀ = ht₀} {.ht₀} (↝-move-reg {n = n} {r} step) th tr (steptype-reg {.ht₀} {τ = τ-ptr τ} q) with step | τ | q | wordFin ≟ n
... | eval-imm | τ-code _ | eτ-imm-ht c | yes refl =
  let record {dis-i = d; insn = insn; fall = fall; safe = s} = safeHeapCode th c
  in th ,
     trUpdate tr
              (reg-code {insns = insn} {fall = fall}
                        (disasMerge {r = Vec.lookup r (Process.registers p₀)} d)
                        s)
              r 
typeStep {p₀} {_} {ht₀} {.ht₀} (↝-move-reg {_} {_} {r} eval-imm) th tr (steptype-reg {.ht₀} {_} {_} {_} {_} {τ-ptr τ} q) | w₁ | w | eτ-imm-ht {i = i} x | yes refl = th , trUpdate tr (reg-direct {lt = ≤-refl} {b = Vec.lookup r (Process.registers p₀)} (~ptr (const-⇒ x))) r
... | _ | _ | qqq | no ¬p with ¬p (lemmer {n = n} qqq)
... | ()

-- If we execute an instruction which just modifies data, the new process is still live
typeStepLive : ∀ {p₀ p₁ : Process} {ht₀ ht₁} {rt₀ rt₁} {insn}
             → Live p₀
             → p₀ ↝⟨ insn ⟩ p₁ # Maybe.nothing
             → ⟨ ht₀ , rt₀ ⟩⇉⟨ insn ⟩⟨ ht₁ , rt₁ ⟩
             → Live p₁
typeStepLive live ↝-halt ()
typeStepLive live (↝-move-mem _) ()
typeStepLive live (↝-move-flag _) ()
typeStepLive live (↝-move-reg _) (steptype-reg _) = live

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

preservation (typed-machine x₁ ht rt (safe-code-fall (eτ-imm-ht px))) (↝-fall {insns = insns} x _ d) with unique-disas d (SafeHeapCode.dis-i (safeHeapCode ht px))
... | refl , refl = typed-machine x ht rt (SafeHeapCode.safe (safeHeapCode ht px))

preservation {record { insn = (jmp (imm i) ∷ _) }} (typed-machine x ht rt (safe-code-jump (eτ-imm-ht px))) (↝-jump {pc' = pc'} live d q) with jmp-to-target {i = i} {pc' = pc'} q
... | refl , refl with unique-disas d (SafeHeapCode.dis-i (safeHeapCode ht px))
... | refl , refl =
    let shc = safeHeapCode ht px
    in typed-machine live ht rt (SafeHeapCode.safe shc)
preservation {record { insn = .(jmp (imm _) ∷ _) }} (typed-machine x ht rt (safe-code-jump (eτ-imm-ht px))) (↝-μStep x₁ ())
preservation {record { insn = .(jmp (imm _) ∷ _) }} (typed-machine x ht rt (safe-code-jump (eτ-imm-ht px))) (↝-fall x₁ () _)

-- If the process p₀ is well typed, and it can evolve to some future process p, then the future process has halted or can take a step.
safety : {p₀ p : Process} → SafeProcess p₀ → p₀ ↝* p → Steps p ⊎ Halted p
safety typing trans = progress (↝*-transport preservation typing trans)
