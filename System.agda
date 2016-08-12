-- This module is a wrapper module pulling all the pieces of the type system
-- and semantics. It is intended to be pulled in by the Safety theorem and by
-- any typing proofs for particular programs.
module System where

open import Process public
open import Semantics public
open import Typing public
open import Disassembly public
open import μOps public
open import Info public
