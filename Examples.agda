-- This module is intended to act as a sort of test suite for the current
-- capabilities of the type system. It gives an idea of how each addition
-- to the type system enables the checking of more code.
module Examples where

-- Halt immediately
import Examples.TrivialHalt
-- Safe register operation, then a halt
import Examples.SimpleHalt
-- Fall through from one instruction to another, then halt
import Examples.SimpleFall
