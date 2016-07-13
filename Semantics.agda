open import Arch using (ArchInfo)

module Semantics (info : ArchInfo) where

open import Process info using (Process; Live; Halted)
open import Data.Nat as Nat using (ℕ; _⊔_; _≤_)
open import Data.Nat.Base as NatBase using ()
open import Data.Vec as Vec using (Vec; _[_]≔_; lookup) renaming (_∷_ to _v∷_)
open import Data.List using (List; _++_; []; _∷_)
open import Data.Fin as Fin using (Fin)
open import Disassembly info
open import Data.Product using (_,_)
open import Memory (ArchInfo.wordSize info)
open import Data.Maybe
open import μOps info
open import Data.Bool
open import Data.BitVector as BitVector using (Bit; BitVector; zero)

wordSize : ℕ
wordSize = ArchInfo.wordSize info

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

data _↝⟨_⟩_#_ : Process → μInsn → Process → Maybe Word → Set
data _↝⟨_⟩*_#_ : Process → List μInsn → Process → Maybe Word → Set
data _↝⟨_⟩_#_ where
  ↝-halt : ∀ {p} → p ↝⟨ halt ⟩ record p {halted = true} # Maybe.nothing
  ↝-move-reg : ∀ {p} {n} {r} {expr} {val}
             → p ⊢ expr ⇝ val
             → p ↝⟨ move {τ-bv (Fin.toℕ n)} (reg r n) expr ⟩
                 record p { registers = (Process.registers p) [ r ]≔ (mergeVec {lt = fin-lt n} (lookup r (Process.registers p)) (μBits val)) } # Maybe.nothing
  ↝-move-mem : ∀ {p} {expr} {val}
             → p ⊢ expr ⇝ val
             → p ↝⟨ move {τ-mem} mem expr ⟩ record p { memory = μMem val } # Maybe.nothing
  ↝-move-flag : ∀ {p} {f} {expr} {val}
              → p ⊢ expr ⇝ val
              → p ↝⟨ move {τ-bv 1} (flag f) expr ⟩ record p { flags = (Process.flags p) [ f ]≔ μBits val } # Maybe.nothing
  ↝-jmp : ∀ {p} {expr} {target}
        → p ⊢ expr ⇝ target
        → p ↝⟨ jmp expr ⟩ p # Maybe.just (μBits target)

data _↝⟨_⟩*_#_ where
  ↝-done : ∀ {p} → p ↝⟨ [] ⟩* p # Maybe.nothing
  ↝-halted : ∀ {p₀ p₁} {insn} {insns} {tgt} → Halted p₁ → p₀ ↝⟨ insn ⟩ p₁ # tgt → p₀ ↝⟨ insn ∷ insns ⟩* p₁ # Maybe.nothing
  ↝-step : ∀ {p₀ p₁ p₂} {insn} {insns} {tgt} {_ : Live p₀} → p₀ ↝⟨ insn ⟩ p₁ # Maybe.nothing → p₁ ↝⟨ insns ⟩* p₂ # tgt → p₀ ↝⟨ insn ∷ insns ⟩* p₂ # tgt
  ↝-esc  : ∀ {p₀ p₁} {insn} {insns} {tgt} {_ : Live p₀} → p₀ ↝⟨ insn ⟩ p₁ # Maybe.just tgt → p₀ ↝⟨ insn ∷ insns ⟩* p₁ # Maybe.just tgt

data _↝_ : Process → Process → Set where
  ↝-fall : ∀ {p p'} {insns} {pc'}
         → Live p
         → (Process.disassembly p) ⟦ Process.pc p ↦⟨ insns , pc' ⟩⟧
         → p ↝⟨ insns ⟩* p' # Maybe.nothing
         → p ↝ record p' { pc = pc' }
  ↝-jump : ∀ {p p'} {insns} {pc'} {dc}
         → Live p
         → (Process.disassembly p) ⟦ Process.pc p ↦⟨ insns , dc ⟩⟧
         → p ↝⟨ insns ⟩* p' # Maybe.just pc'
         → p ↝ record p' { pc = pc' }

--Any process which takes a step is live
live-step : ∀ {p p' : Process} → p ↝ p' → Live p
live-step (↝-fall live _ _) = live
live-step (↝-jump live _ _) = live

data _↝*_ : Process → Process → Set where
  ↝*-nop : {p : Process} → p ↝* p
  ↝*-extend : {p₀ p₁ p₂ : Process} → p₀ ↝* p₁ → p₁ ↝ p₂ → p₀ ↝* p₂

-- If we can move a property across ↝, we can move it across ↝*. 
↝*-transport : {p₀ p₁ : Process} → {P : Process → Set} → (step : {p₀ p₁ : Process} → P p₀ → p₀ ↝ p₁ → P p₁) → P p₀ → p₀ ↝* p₁ → P p₁
↝*-transport step base ↝*-nop = base
↝*-transport step base (↝*-extend trans x) = step (↝*-transport step base trans) x
