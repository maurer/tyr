open import Arch

--ARM 32
info : ArchInfo
info = record {
    wordSize = 32;
    numRegs = 16;
    numFlags = 4
  }
