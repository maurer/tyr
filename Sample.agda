open import Arch
open import Info
open ArchInfo info

module _ where
  open import Data.Fin hiding (_<_)
  open import Data.Nat

  FlagId = Fin numFlags
  fidNeg : FlagId
  fidNeg = raise 3 (fromℕ 0)
  fidZero : FlagId
  fidZero = raise 2 (fromℕ 1)
  fidCarry : FlagId
  fidCarry = raise 1 (fromℕ 2)
  fidOverflow : FlagId
  fidOverflow = fromℕ 3

  RegId = Fin numRegs
  rid0  : RegId
  rid0  = raise 15 (fromℕ 0)
  rid3  : RegId
  rid3  = raise 12 (fromℕ 3)
  rid11 : RegId
  rid11 = raise 4 (fromℕ 11)
  rid13 : RegId
  rid13 = raise 2 (fromℕ 13)
  rid14 : RegId
  rid14 = raise 1 (fromℕ 14)
  ridSp : RegId
  ridSp = rid13
  ridLr : RegId
  ridLr = rid14

  open import μOps info

  ridToVar : RegId → Var (τ-bv wordSize)
  ridToVar rid = reg rid (fromℕ wordSize)

open import μOps info
open import Data.List
open import Data.Integer
open import Data.BitVector renaming (-_ to b-_)
open import Data.Nat using (ℕ; suc)
open import Data.Sign using (Sign)
open import Data.BitVector.Peano using (fromℕ; toℕ)
open import Data.Vec as Vec using ()

{-
int main (int argc) {
  return 2 * argc;
}
-}

RegVar = Var (τ-bv wordSize)

r0 : RegVar
r0 = ridToVar rid0

r3 : RegVar
r3 = ridToVar rid3

r11 : RegVar
r11 = ridToVar rid11

sp : RegVar
sp = ridToVar ridSp

lr : RegVar
lr = ridToVar ridLr

fromNeg : (n : ℕ) → ℤ
fromNeg 0 = + 0
fromNeg (suc n) = -[1+ n ]

$_ : ∀ {τ} → Var τ → Expr τ
$_ = evar

{-# BUILTIN FROMNEG fromNeg #-}

-- This is only a convenience notation - if the input is out of bounds, behavior is dumb
fromℤ : ∀ {n} → ℤ → BitVector n
fromℤ {l} i with signAbs i
fromℤ .(Sign.- ◃ n) | Sign.- ◂ n = b- (fromℕ n)
fromℤ .(Sign.+ ◃ n) | Sign.+ ◂ n = fromℕ n

#_ : ∀ {n} → ℤ → Expr (τ-bv n)
#_ {len} val = imm (fromℤ {len} val)

main : List μInsn
main =
  -- str r11, [sp, #-4]!
  move mem (($ mem) ⟦ ($ sp) ⊕⟨ ⊕ ⟩ (# -4) ↦ ($ r11) ⟧) ∷
  move sp (($ sp) ⊕⟨ ⊕ ⟩ (# -4)) ∷
  -- add r11, sp, #0x0
  move r11 ($ sp) ∷
  -- sub sp, sp, #0xc
  move sp (($ sp) ⊕⟨ ⊖ ⟩ (# (+ 0xc))) ∷
  -- str r0, [r11, #-8]
  move mem (($ mem) ⟦ ($ r11) ⊕⟨ ⊕ ⟩ (# -8) ↦ ($ r0) ⟧) ∷
  -- ldr r3, [r11, #-8]
  move r3 (($ mem) ⟦ ($ r11) ⊕⟨ ⊕ ⟩ (# -8) ⟧⟨ 4 ⟩) ∷
  -- lsl r3, r3, #1
  move r3 (($ r3) ⊕⟨ ⟪ ⟩ (# (+ 1))) ∷
  -- mov r0, r3
  move r0 ($ r3) ∷
  -- sub sp, r11, #0x0
  move sp ($ r11) ∷
  -- ldr r11, [sp], #4
  move r11 (($ mem) ⟦ $ sp ⟧⟨ 4 ⟩) ∷
  move sp (($ sp) ⊕⟨ ⊕ ⟩ (# (+ 4))) ∷
  jmp ($ lr) ∷
  []

open import Process info

scaffoldSema : Word → Word → Word → List μInsn
scaffoldSema mainAddr haltAddr stackAddr =
  move lr (imm haltAddr) ∷
  move sp (imm stackAddr) ∷
  jmp (imm mainAddr) ∷
  []

open import Data.Bool as Bool using ()

mainLoadAddr : Word
mainLoadAddr = fromℕ 0x8000

startLoadAddr : Word
startLoadAddr = fromℕ 0x1000

haltLoadAddr : Word
haltLoadAddr = fromℕ 0

stackLoadAddr : Word
stackLoadAddr = fromℕ 0xFFFFFFFF

stackBaseAddr : Word
stackBaseAddr = fromℕ 0xF0000000

open import Data.Nat as Nat using ()

stackLen : ℕ
stackLen = (toℕ stackLoadAddr) Nat.+ (toℕ stackBaseAddr) Nat.+ 1

open import Disassembly info
open import Data.Maybe as Maybe
open import Data.Product

scaffoldDisasm : List μInsn → Disassembly
scaffoldDisasm main =
  (haltLoadAddr , ([ halt ] , Maybe.nothing)) ∷
  (startLoadAddr , (scaffoldSema mainLoadAddr haltLoadAddr stackLoadAddr , Maybe.nothing)) ∷
  (mainLoadAddr , (main , Maybe.nothing)) ∷
  []

open import Memory wordSize
scaffoldMem : Memory
scaffoldMem =
  -- Stack
  (seg stackBaseAddr stackLen (Vec.replicate (zero byteWidth)) RW) ∷
  []

scaffold : List μInsn → Process
scaffold main = record {
    registers = Vec.replicate (zero wordSize);
    flags = Vec.replicate (zero 1);
    pc = startLoadAddr;
    disassembly = scaffoldDisasm main;
    memory = scaffoldMem;
    halted = Bool.false
  }

sample : Process
sample = scaffold main

open import Typing info
sampleSafety : SafeProcess sample
sampleSafety = {!!}

open import Semantics info
open import Safety info
open import Data.Sum
samplePolicy : ∀ {future} → sample ↝* future → Steps future ⊎ Halted future
samplePolicy = safety sampleSafety
