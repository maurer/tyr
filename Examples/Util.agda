-- This module essentially brings into scope the set of functions useful for
-- manually writing semantics and types for the purpose of writing checked
-- examples.
module Examples.Util where

-- Pull in the type system
open import System public

-- Pull in useful pieces for constructing certificates
open import Relation.Binary.PropositionalEquality using (refl) public
open import Data.BitVector.Peano renaming (fromℕ to word;
                                           toℕ to projWord) public
open import Data.BitVector using (zero; BitVector) public
open import Data.Bool using (true; false) public
open import Data.List using ([_]; []; _∷_) public
open import Data.Product using (_,_; proj₁; proj₂) public
open import Data.Maybe using (just; nothing) public
open import Data.Vec using (replicate; _[_]≔_) renaming (_∷_ to _v∷_) public
open import Data.List.Any using (here; there) public
open import Data.Integer using (+_; -_) public

-- Pieces needed to construct helpers
open import Data.Nat using (ℕ; _≤_)
open import Data.Integer using (ℤ; -[1+_]; signAbs; _◃_; _◂_)
open import Data.Sign using (Sign)
open import Data.BitVector renaming (-_ to b-_)
open import Relation.Binary.PropositionalEquality using (subst; _≡_)
open import Relation.Binary using (DecTotalOrder)
open import Data.Vec as Vec using (Vec)
open import Data.Fin using (Fin; raise; fromℕ)

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {ℕ.zero} = _≤_.z≤n
≤-refl {ℕ.suc n} = _≤_.s≤s ≤-refl

-- Any value is a legal ⊤ in a register
reg-⊤ : ∀ {v : Word} {ht} {d} → TypedRegister v ht d τ-⊤
reg-⊤ {v} {ht} {d} =
  subst (λ v → TypedRegister v ht d τ-⊤)
        (mergeVecFullEq {lt = ≤-refl} {v = zeroWord} {v' = v})
        (reg-direct {v = v} {lt = ≤-refl} {b = zeroWord} ~⊤)

-- Generate a trivial typing of any register vector as all ⊤
⊤-regs : ∀ {len} {disas}
       → (regs : Vec Word len)
       → (ht : HeapType)
       → TypedRegisters regs ht disas (replicate τ-⊤)
⊤-regs Vec.[] _ = regs-nil
⊤-regs (v v∷ vs) ht = regs-cons reg-⊤ (⊤-regs vs ht)

-- Flag literals
falseFlag = Vec.[ false ]
trueFlag = Vec.[ true ]

-- Convenience function to allow integer literals to be ℤ.
fromNeg : (n : ℕ) → ℤ
fromNeg 0 = + 0
fromNeg (ℕ.suc n) = -[1+ n ]

-- This bit of magic tells Agda to use the above for parsing integer literals.
{-# BUILTIN FROMNEG fromNeg #-}

-- bvFromℤ creates a BitVector of the requested length from a provided member of
-- ℤ. It is only well behaved if the requested BitVector is long enough to hold
-- the value. It is for use in creating easy BitVector literals.
bvFromℤ : ∀ {n} → ℤ → BitVector n
bvFromℤ {l} i with signAbs i
bvFromℤ .(Sign.- ◃ n) | Sign.- ◂ n = b- (word n)
bvFromℤ .(Sign.+ ◃ n) | Sign.+ ◂ n = word n

-- The # prefix operator promotes integers to expressions, e.g. # (- 8) or
-- # (+ 1). The sign is mandatory to convince Agda to lift to an element of ℤ
-- rather than ℕ. It is intended to be reminiscent of AT&T syntax.
#_ : ∀ {n} → ℤ → Expr (τ-bv n)
#_ {len} val = imm (bvFromℤ {len} val)

-- The $ prefix operator promotes variables to expressions, e.g. $ r0
-- It is intended to be reminiscent of AT&T syntax.
$_ : ∀ {τ} → Var τ → Expr τ
$_ = evar

-- Shorthand for various registers
-- Flag IDs
fidNeg      = raise 3 (fromℕ 0)
fidZero     = raise 2 (fromℕ 1)
fidCarry    = raise 1 (fromℕ 2)
fidOverflow = fromℕ 3

-- GPR IDs
rid0  = raise 15 (fromℕ 0)
rid3  = raise 12 (fromℕ 3)
rid11 = raise 4 (fromℕ 11)
rid13 = raise 2 (fromℕ 13)
rid14 = raise 1 (fromℕ 14)
ridSp = rid13
ridLr = rid14

RegId = Fin numRegs
-- Converter from a GPR ID to a variable
ridToVar : RegId → Var (τ-bv wordSize)
ridToVar rid = reg rid (fromℕ wordSize)

-- GPR Variables
r0  = ridToVar rid0
r3  = ridToVar rid3
r11 = ridToVar rid11
sp  = ridToVar ridSp
lr  = ridToVar ridLr
