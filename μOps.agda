-- This module describes the restricted subset of BIL we reason over.
-- Specifically, it is BIL sans temporaries and loops. Currently, loops are not
-- used in lifting, and without loops, temporaries can be removed via
-- substitution, and so this transform can be performed before reasoning about
-- the program.
-- Additionally, we currently ignore cpu exceptions and specials. In theory we
-- could eventuallly reason about cpu exceptions, but specials are fundamentally
-- undefined behavior, and so are not possible to prove over.
open import Info
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.BitVector using (BitVector)
open import Data.List

open import Memory

-- μTypes are the type of a BIL value. This has nothing to do with the type
-- system for checking safety, and instead just refer to the shape of the actual
-- data in question.
data μType : Set where
  -- A bitvector of the specified size
  τ-bv : ℕ → μType
  -- A version of memory
  τ-mem : μType

-- Shorthand for a system word
τ-word = τ-bv wordSize
-- Shorthand for a system address
τ-addr = τ-bv wordSize
-- Shorthand for a flag
τ-flag = τ-bv 1

-- μVal is a typed sum of bitvectors and memory, since BIL values are
-- potentially either.
data μVal : μType → Set where
  val-bits : ∀ {n} → BitVector n → μVal (τ-bv n)
  val-mem  : Memory → μVal τ-mem

-- If we know the type of a μVal is a bitvector, μBits can project it out
μBits : ∀ {n} → μVal (τ-bv n) → BitVector n
μBits (val-bits x) = x

-- If we know the type of a μVal is memory, μMem can project it out
μMem : μVal τ-mem → Memory
μMem (val-mem x) = x

-- BIL Variables
data Var : μType →  Set where
  -- GPR variable
  reg  : (idx : Fin numRegs)           -- Register index
       → (len : Fin (suc wordSize))    -- How many bits of register to use (low)
       → Var (τ-bv (Data.Fin.toℕ len))
  -- Flag variable
  flag : (idx : Fin numFlags) → Var (τ-bv 1)
  -- Memory variable
  mem  : Var τ-mem

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
  -- TODO get better symbols for these,
  cmp-<  : CmpOp
  cmp-≤  : CmpOp
  cmp-±< : CmpOp
  cmp-±≤ : CmpOp

data UnOp : Set where
  ±-   : UnOp -- Twos Complement Numerical Negation
  un-¬ : UnOp -- Bitwise Negation

data Expr : μType → Set where
  -- BinOp
  _⊕⟨_⟩_ : ∀ {τ} → Expr τ → BinOp → Expr τ → Expr τ
  -- Comparison
  _?⟨_⟩_ : ∀ {τ} → Expr τ → CmpOp → Expr τ → Expr τ-flag
  -- UnOp
  _$$_ : ∀ {τ} → UnOp → Expr τ → Expr τ
  evar : ∀ {τ} → Var τ → Expr τ
  imm : ∀ {n : ℕ} → BitVector n → Expr (τ-bv n)
  -- Read
  _⟦_⟧⟨_⟩ : (mem : Expr τ-mem) → (addr : Expr τ-addr) → (size : ℕ)
          → Expr (τ-bv size)
  -- Write
  _⟦_↦_⟧ : ∀ {size : ℕ} → (mem : Expr τ-mem) → (addr : Expr τ-addr)
           → (value : Expr (τ-bv size)) → Expr τ-mem
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
