-- This module is intended to model a system's memory via the Read and Write
-- predicates. The internal representation is very much in flux, and is probably
-- not yet in a good place.

-- At the moment, the primary thing this module provides is an existing Memory
-- type along with Read and Write predicates to act as placeholders in other
-- rules.

-- TODO: Actually implement Read/Write, non-overlapping segments

open import Data.BitVector using (BitVector; _+_; -_; one)
open import Data.BitVector.NumericOrder using (_≤_)
open import Data.BitVector.Peano using (toℕ; fromℕ)
open import Data.Fin using (Fin; fromℕ≤)
open import Relation.Binary using (StrictTotalOrder)
open import Data.Nat using (ℕ; _≤?_; z≤n) renaming (_+_ to _ℕ+_; _<_ to _ℕ<_)
open import Data.Nat.DivMod using (_div_)
open import Data.Vec using (Vec; lookup; _++_)
open import Data.List using (List; _∷_)
import Data.Maybe as Maybe

open import Info

module Memory where

-- We assume the memory address bus is the same size as the GPR
width = wordSize
Addr = BitVector width

-- A byte is the minimum readable size from memory, 8 bits
byteWidth = 8
Byte = BitVector byteWidth

-- Perms is the permissions for a given memory segment. Since we do not
-- currently support writing to a code segment, WX is not present.
data Perms : Set where
  RX : Perms
  RW : Perms
  RO : Perms

-- The Readable/Writable/Executable predicates are abstractions over the
-- structure of Perms to avoid casing out.
data Readable : Perms → Set where
  readable-all : ∀ {p} → Readable p

data Writable : Perms → Set where
  writable-rw : Writable RW

data Executable : Perms → Set where
  executable-rx : Executable RX

-- A Segment is a base address, segment contents, and permissions
data Segment : Set where
  seg : Addr → (n : ℕ) → Vec Byte n → Perms → Segment

-- Memory is a list of segments, which do not overlap
-- The non-overlapping is not yet encoded, which is part of why this module
-- is not fully functional yet
Memory = List Segment

-- ReadSeg indicates that you can perform a read of a segment and get a given
-- result, while within bounds
data ReadSeg : Segment → Addr → (len : ℕ) → BitVector len → Set where

-- As ReadSeg, but for a Memory
data Read : Memory → Addr → (len : ℕ) → BitVector len → Set where

-- WriteSeg indicates that a write is in bounds for a segment, and that after
-- the write, the new segment in the predicate will be the result
data WriteSeg : Segment → Addr → (len : ℕ) → BitVector len → Segment → Set where

-- As WriteSeg, but for a Memory
data Write : Memory → Addr → (len : ℕ) → BitVector len → Memory → Set where
