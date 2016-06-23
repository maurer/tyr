open import Arch using (ArchInfo)

module Typing (info : ArchInfo) where

open import Data.Nat using (ℕ)

open import Process info using (Process)
open import Semantics info as Semantics
open IntraInstruction

open import μOps
open import Data.List using (_∷_)

data Typed : Process → Set
data IntraTyped : {n : ℕ} → IntraInsnProcess {n} → Set

data Typed where
  typed-intra : ∀ {p} {n} {i : IntraInsnProcess {n}} → p ↑ i → IntraTyped i → Typed p

data IntraTyped where
  intra-done : ∀ {n} {i : IntraInsnProcess {n}} {p} → i ↓ p → Typed p → IntraTyped i
  intra-halt : ∀ {n} {p} {t} {μOps} → IntraTyped {n} record {process = p; temps = t; sema = halt ∷ μOps}
