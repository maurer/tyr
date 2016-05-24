open import Data.BitVector using (BitVector)
import Data.BitVector.NumericOrder as BVNO
open import Relation.Binary using (StrictTotalOrder)
open import Data.Nat using (ℕ)

module Memory (width : ℕ) where

  Byte = BitVector 8

  import Data.AVL (λ _ → Byte) (StrictTotalOrder.isStrictTotalOrder (BVNO.strictTotalOrder {n = width})) as BVAVL
  
  Memory = BVAVL.Tree
  
