-- This module contains the main safety theorem. In a nutshell, if a process is
-- well typed, then any process it can evolve into has either halted or can take
-- a step.
module Safety where

open import System

-- Progress Lemma
open import Safety.Progress
-- Preservation Lemma
open import Safety.Preservation

open import Data.Sum using (_⊎_)

-- If the process p₀ is well typed, and it can evolve to some future process p,
-- then the future process has halted or can take a step.
safety : {p₀ p : Process} → SafeProcess p₀ → p₀ ↝* p → Steps p ⊎ Halted p
safety typing trans = progress (↝*-transport preservation typing trans)
