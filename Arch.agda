open import Data.Nat using (ℕ)

-- An ArchInfo structure contains the information needed to describe the state
-- of a process running on the architecture
--
-- In the future, it is intended to functorize all the modules over this
-- structure, but the emacs mode and error reporting work poorly with
-- functorized modules, so I'm explicitly using a particular instance of
-- `ArchInfo` everywhere for the moment.
-- FUTURE: Functorize modules over `ArchInfo`
record ArchInfo : Set where
  field
    -- Width of GPRs and address bus, assumed to be the same
    wordSize : ℕ
    -- Number of GPRs
    numRegs  : ℕ
    -- Number of condition flags
    numFlags : ℕ
