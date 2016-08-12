-- This module provides architecture information for ARM32. In the long run, it
-- is intended to provide a variety of architecture templates once the system
-- is functorized.
-- FUTURE: Once functorized, provide multiple architectures, remove exports

open import Arch
open import Data.BitVector using (BitVector; zero)

-- ARM 32
info : ArchInfo
info = record {
    wordSize = 32;
    numRegs = 16;
    numFlags = 4
  }

-- Re-export fields - I was opening this module in every file otherwise
open ArchInfo info public

-- A Word is a BitVector the width of the GPR or the address bus 
Word = BitVector wordSize

-- zeroWord is a convenience alias for a zero'd out Word
zeroWord : Word
zeroWord = zero wordSize
