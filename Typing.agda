open import Arch using (ArchInfo)

module Typing (info : ArchInfo) where

open import Process info using (Process)

data Typed : Process → Set where
