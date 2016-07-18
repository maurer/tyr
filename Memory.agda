open import Data.BitVector using (BitVector; _+_; -_; one)
open import Data.BitVector.NumericOrder using (_≤_)
open import Data.BitVector.Peano using (toℕ; fromℕ)
open import Data.Fin using (Fin; fromℕ≤)
open import Relation.Binary using (StrictTotalOrder)
open import Data.Nat using (ℕ; _≤?_; z≤n) renaming (_+_ to _ℕ+_; _<_ to _ℕ<_)
open import Data.Nat.DivMod using (_div_)
open import Data.Vec using (Vec; lookup; _++_)
open import Data.List using (List; _∷_)
open import Value
import Data.Maybe as Maybe

open import Info
open import Arch

module Memory  where

  width = ArchInfo.wordSize info

  byteWidth : ℕ
  byteWidth = 8

  Byte = BitVector byteWidth

  Addr = BitVector width

  data Perms : Set where
    RX : Perms
    RW : Perms
    RO : Perms

  data Readable : Perms → Set where
    readable-all : ∀ {p} → Readable p

  data Writable : Perms → Set where
    writable-rw : Writable RW

  data Executable : Perms → Set where
    executable-rx : Executable RX

  data Segment : Set where
    seg : Addr → (n : ℕ) → Vec Byte n → Perms → Segment

  Memory = List Segment

  data ReadSeg : Segment → Addr → (len : ℕ) → BitVector len → Set where
    read-seg-byte : ∀ {base : Addr} {segLen : ℕ} {dat} {perm} {addr} {base}
                  → Readable perm
                  → (lower : base ≤ addr)
                  → (upper :  toℕ (addr + - base) ℕ< segLen)
                  → ReadSeg (seg base segLen dat perm) addr byteWidth (lookup (fromℕ≤ upper) dat)

  data Read : Memory → Addr → (len : ℕ) → BitVector len → Set where
    read-expand : ∀ {seg} {mem} {addr} {len} {dat}
                → Read mem addr len dat
                → Read (seg ∷ mem) addr len dat
    read-head : ∀ {seg} {segs} {addr} {len} {dat}
              → ReadSeg seg addr len dat
              → Read (seg ∷ segs) addr len dat
    read-concat : ∀ {m} {addr} {len₀ len₁} {bits₀ : BitVector len₀} {bits₁ : BitVector len₁}
                → Read m addr len₀ bits₀
                → Read m (addr + fromℕ (len₀ div byteWidth)) len₁ bits₁
                → Read m addr (len₀ ℕ+ len₁) (bits₀ ++ bits₁)

  data WriteSeg : Segment → Addr → (len : ℕ) → BitVector len → Memory → Set where

  data Write : Memory → Addr → (len : ℕ) → BitVector len → Memory → Set where
