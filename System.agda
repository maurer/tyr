open import Arch using (ArchInfo)
module System (info : ArchInfo) where

open import Process info public
open import Semantics info public
open import Typing info public
