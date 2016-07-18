open import Arch

--ARM 32
info : ArchInfo
info = record {
    wordSize = 4;
    numRegs = 16;
    numFlags = 4
  }
