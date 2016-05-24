open import Data.Nat using (ℕ)

record ArchInfo : Set where
  field
    wordSize : ℕ
    numRegs  : ℕ
    numFlags : ℕ
