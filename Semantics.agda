open import Arch using (ArchInfo)
open import Info
module Semantics where

open import Process using (Process; Live; Halted)
open import Data.Nat as Nat using (ℕ; _⊔_; _≤_; suc)
open import Data.Nat.Base as NatBase using ()
open import Data.Vec as Vec using (Vec; _[_]≔_; lookup) renaming (_∷_ to _v∷_)
open import Data.List using (List; _++_; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Data.Fin as Fin using (Fin)
open import Disassembly
open import Data.Product using (_,_; _×_)
open import Memory
open import Data.Maybe
open import μOps
open import Data.Bool
open import Data.BitVector as BitVector using (Bit; BitVector; zero)
open ArchInfo info

--TODO this definition needs to be killed
μUndef : ∀ {n} → μVal (τ-bv n)
μUndef {n} = val-bits (zero n)

--TODO INCOMPLETE
runBinOp : ∀ {n} → BinOp → μVal (τ-bv n) → μVal (τ-bv n) → μVal (τ-bv n)
runBinOp _ _ _ = μUndef

--TODO INCOMPLETE
runUnOp : ∀ {n} → UnOp → μVal (τ-bv n) → μVal (τ-bv n)
runUnOp _ _ = μUndef

--TODO INCOMPLETE
runCmpOp : ∀ {n} → CmpOp → μVal (τ-bv n) → μVal (τ-bv n) → μVal τ-flag
runCmpOp _ _ _ = μUndef

subVec : ∀ {n : ℕ} {A : Set} → (l : Fin (Nat.suc n)) → Vec A n → Vec A (Fin.toℕ l)
subVec Fin.zero _ = Vec.[]
subVec (Fin.suc l) (x v∷ xs) = x v∷ subVec l xs
subVec {.Nat.zero} {_} (Fin.suc {.Nat.zero} ()) Vec.[]

data _⊢_⇝_ : ∀ {τ} → Process → Expr τ → μVal τ → Set where
  eval-binop : ∀ {p} {n} {e₁ e₂ : Expr (τ-bv n)} {v₁ v₂} {op}
             → p ⊢ e₁ ⇝ v₁
             → p ⊢ e₁ ⇝ v₂
             → p ⊢ e₁ ⊕⟨ op ⟩ e₂ ⇝ runBinOp op v₁ v₂
  eval-unop : ∀ {p} {n} {e : Expr (τ-bv n)} {v} {op}
            → p ⊢ e ⇝ v
            → p ⊢ op $$ e ⇝ runUnOp op v
  eval-cmp : ∀ {p} {n} {e₁ e₂ : Expr (τ-bv n)} {v₁ v₂} {op}
           → p ⊢ e₁ ⇝ v₁
           → p ⊢ e₂ ⇝ v₂
           → p ⊢ e₁ ?⟨ op ⟩ e₂ ⇝ runCmpOp op v₁ v₂
  eval-evar-reg : ∀ {p} {idx} {len}
                → p ⊢ evar (reg idx len) ⇝ val-bits (subVec len (Vec.lookup idx (Process.registers p)))
  eval-evar-flag : ∀ {p} {idx}
                 → p ⊢ evar (flag idx) ⇝ val-bits (Vec.lookup idx (Process.flags p))
  eval-evar-mem : ∀ {p}
                → p ⊢ evar mem ⇝ val-mem (Process.memory p)
  eval-imm : ∀ {p} {n} {v : BitVector n}
           → p ⊢ imm v ⇝ val-bits v
  eval-load : ∀ {p} {eMem} {vMem} {eAddr} {vAddr} {size} {dat}
            → p ⊢ eMem ⇝ vMem
            → p ⊢ eAddr ⇝ vAddr
            → Read (μMem vMem) (μBits vAddr) size dat
            → p ⊢ eMem ⟦ eAddr ⟧⟨ size ⟩ ⇝ val-bits dat
  eval-store : ∀ {p} {eMem} {vMem} {eAddr} {vAddr} {size} {eDat : Expr (τ-bv size)} {vDat} {mem'}
             → p ⊢ eMem ⇝ vMem
             → p ⊢ eAddr ⇝ vAddr
             → p ⊢ eDat ⇝ vDat
             → Write (μMem vMem) (μBits vAddr) size (μBits vDat) mem'
             → p ⊢ eMem ⟦ eAddr ↦ eDat ⟧ ⇝ val-mem mem'

fin-lt : ∀ {n} → (x : Fin (Nat.suc n)) → (Fin.toℕ x) ≤ n
fin-lt Fin.zero = _≤_.z≤n
fin-lt {Nat.suc n} (Fin.suc x) = Nat.s≤s (fin-lt x)
fin-lt (Fin.suc {Nat.zero} ())

mergeVec : ∀ {m n} {A : Set} {lt : m ≤ n} → Vec A n → Vec A m → Vec A n
mergeVec {lt = Nat.s≤s lt} (x v∷ xs) (y v∷ ys) = y v∷ mergeVec {lt = lt} xs ys
mergeVec xs Vec.[] = xs

mergeVecFullEq : ∀ {n} {A} {lt} {v v'} → mergeVec {n} {n} {A} {lt} v v' ≡ v'
mergeVecFullEq {n = 0} {lt = Nat.z≤n} {v = Vec.[]} {Vec.[]} = refl
mergeVecFullEq {n = suc n} {lt = Nat.s≤s lt} {v = x v∷ v} {v' = x' v∷ v'} =
  cong₂ _v∷_ refl (mergeVecFullEq {lt = lt})

setReg : Process → Fin numRegs → (l : Fin (ℕ.suc wordSize)) → μVal (τ-bv (Fin.toℕ l)) → Process
setReg p r len val = record p { registers = (Process.registers p) [ r ]≔ (mergeVec {lt = fin-lt len} (lookup r (Process.registers p)) (μBits val)) }

data _↝⟨_⟩_#_ : Process → μInsn → Process → Maybe Word → Set where
  ↝-halt : ∀ {p} → p ↝⟨ halt ⟩ record p {halted = true} # Maybe.nothing
  ↝-move-reg : ∀ {p} {n} {r} {expr : Expr (τ-bv (Fin.toℕ n))} {val}
             → p ⊢ expr ⇝ val
             → p ↝⟨ move {τ-bv (Fin.toℕ n)} (reg r n) expr ⟩
                 setReg p r n val # Maybe.nothing
  ↝-move-mem : ∀ {p} {expr} {val}
             → p ⊢ expr ⇝ val
             → p ↝⟨ move {τ-mem} mem expr ⟩ record p { memory = μMem val } # Maybe.nothing
  ↝-move-flag : ∀ {p} {f} {expr} {val}
              → p ⊢ expr ⇝ val
              → p ↝⟨ move {τ-bv 1} (flag f) expr ⟩ record p { flags = (Process.flags p) [ f ]≔ μBits val } # Maybe.nothing
  ↝-jmp : ∀ {p} {expr} {target}
        → p ⊢ expr ⇝ target
        → p ↝⟨ jmp expr ⟩ p # Maybe.just (μBits target)

jmp-to-target : ∀ {p} {p'} {i} {pc'}
              → p ↝⟨ jmp (imm i) ⟩ p' # Maybe.just pc'
              → (i ≡ pc') × (p ≡ p')
jmp-to-target (↝-jmp eval-imm) = refl , refl

data InsnDone : Process → Set where
  proc-done : ∀ {p} → InsnDone record p {insn = []}

data _↝_ : Process → Process → Set where
  {-
   TODO the fall setting shouldn't be necessary in the constructor
   It's there to make some proofs easier, for now, but it should be derivable by looking at the second term passed to μStep
  -}
  ↝-μStep : ∀ {p p'} {insn} {insns}
          → Live p
          → p ↝⟨ insn ⟩ p' # Maybe.nothing
          → record p {insn = insn ∷ insns} ↝ record p' {insn = insns; fall = Process.fall p}
  ↝-fall : ∀ {p} {insns} {pc'}
         → Live p
         → InsnDone p
         → (Process.disassembly p) ⟦ Process.fall p ↦⟨ insns , pc' ⟩⟧
         → p ↝ record p { pc = Process.fall p; fall = pc'; insn = insns }
  ↝-jump : ∀ {p p'} {insn} {rest} {insns} {pc'} {fall}
         → Live p
         → (Process.disassembly p) ⟦ pc' ↦⟨ insns , fall ⟩⟧
         → p ↝⟨ insn ⟩ p' # Maybe.just pc'
         → record p {insn = insn ∷ rest} ↝ record p' { pc = pc'; fall = fall; insn = insns}

--Any process which takes a step is live
live-step : ∀ {p p' : Process} → p ↝ p' → Live p
live-step (↝-μStep live _) = live
live-step (↝-fall live _ _) = live
live-step (↝-jump live _ _) = live

data _↝*_ : Process → Process → Set where
  ↝*-nop : {p : Process} → p ↝* p
  ↝*-extend : {p₀ p₁ p₂ : Process} → p₀ ↝* p₁ → p₁ ↝ p₂ → p₀ ↝* p₂

-- If we can move a property across ↝, we can move it across ↝*. 
↝*-transport : {p₀ p₁ : Process} → {P : Process → Set} → (step : {p₀ p₁ : Process} → P p₀ → p₀ ↝ p₁ → P p₁) → P p₀ → p₀ ↝* p₁ → P p₁
↝*-transport step base ↝*-nop = base
↝*-transport step base (↝*-extend trans x) = step (↝*-transport step base trans) x
