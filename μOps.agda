open import Arch using (ArchInfo)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.BitVector using (BitVector)
open import Data.List

module μOps (info : ArchInfo) where

open import Memory (ArchInfo.wordSize info)

data μType : Set where
  τ-bv : ℕ → μType
  τ-mem : μType

τ-word = τ-bv (ArchInfo.wordSize info)
τ-addr = τ-bv (ArchInfo.wordSize info)
τ-flag = τ-bv 1

data μVal : μType → Set where
  val-bits : ∀ {n} → BitVector n → μVal (τ-bv n)
  val-mem  : Memory → μVal τ-mem

μBits : ∀ {n} → μVal (τ-bv n) → BitVector n
μBits (val-bits x) = x

μMem : μVal τ-mem → Memory
μMem (val-mem x) = x

data Var : μType →  Set where
  reg  : (idx : Fin (ArchInfo.numRegs info)) → (len : Fin (suc (ArchInfo.wordSize info))) → Var (τ-bv (Data.Fin.toℕ len))
  flag : (idx : Fin (ArchInfo.numFlags info)) → Var (τ-bv 1)
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
  imm : ∀ {n : ℕ} → BitVector n → Expr (τ-bv n)
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
