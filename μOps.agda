open import Arch using (ArchInfo)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Value using (Value; undef)
open import Data.List

module μOps (info : ArchInfo) (numTemps : ℕ) where

data μType : Set where
  τ-bv : ℕ → μType
  τ-mem : μType

τ-word = τ-bv (ArchInfo.wordSize info)
τ-addr = τ-bv (ArchInfo.wordSize info)
τ-flag = τ-bv 1

data Var : μType →  Set where
  reg  : (idx : Fin (ArchInfo.numRegs info)) → (len : ℕ) → Var (τ-bv len)
  flag : (idx : Fin (ArchInfo.numFlags info)) → Var (τ-bv 1)
  temp :  (idx : Fin numTemps) → (len : ℕ) → Var (τ-bv len)
  mem  :  Var τ-mem

data BinOp : Set where
  ⊕  : BinOp -- Addition
  ⊖  : BinOp -- Subtraction
  ⊗  : BinOp -- Multiplication
  ⊘  : BinOp -- Division
  ±⊘ : BinOp -- Signed Division
  %  : BinOp -- Modulo
  ±% : BinOp -- Signed modulo
  ⟪  : BinOp -- Bitshift Left
  ⟫  : BinOp -- Bitshift Right
  ±⟫ : BinOp -- Arithmetic Bitshift Right
  bop-&  : BinOp -- Bitwise And
  bop-|  : BinOp -- Bitwise Or
  bop-^  : BinOp -- Bitwise Xor

data CmpOp : Set where
  ≗  : CmpOp -- Bitvector Equality
  ¬≗ : CmpOp -- Bitvector Inequality
  --TODO get better symbols for these,
  cmp-<  : CmpOp
  cmp-≤  : CmpOp
  cmp-±< : CmpOp
  cmp-±≤ : CmpOp

data UnOp : Set where
  ±-   : UnOp -- Twos Complement Numerical Negation
  un-¬ : UnOp -- Bitwise Negation

data Expr : μType → Set where
  _⊕⟨_⟩_ : ∀ {τ} → Expr τ → BinOp → Expr τ → Expr τ
  _?⟨_⟩_ : ∀ {τ} → Expr τ → CmpOp → Expr τ → Expr τ-flag
  _$$_ : ∀ {τ} → UnOp → Expr τ → Expr τ
  evar : ∀ {τ} → Var τ → Expr τ
  imm : ∀ {n : ℕ} → Value n → Expr (τ-bv n)
  _⟦_⟧⟨_⟩ : (mem : Expr τ-mem) → (addr : Expr τ-addr) → (size : ℕ) → Expr (τ-bv size)
  _⟦_↦_⟧ : ∀ {size : ℕ} → (mem : Expr τ-mem) → (addr : Expr τ-addr) → (value : Expr (τ-bv size)) → Expr τ-mem
  {- unimpl
  let_=_in_ : ∀ {τ τ'} → Var τ → Expr τ → Expr τ' → Expr τ'
  ite
  extract
  concat
  -}

data μInsn : Set where
  halt : μInsn
  move : ∀ {τ : μType} → Var τ → Expr τ → μInsn
  jmp  : Expr τ-addr → μInsn
  cond : Expr τ-flag
       → (thenClause : List μInsn)
       → (elseClause : List μInsn)
       → μInsn
  cpu-exn : ℕ → μInsn
  {- unimpl
  -- Impossible to prove anything about
  special : String → μInsn
  -- Should be unrolled
  while : Expr τ-flag → List μInsn → μInsn
  -}
