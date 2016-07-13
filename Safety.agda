open import Data.Sum
open import Data.Product
open import Data.Bool using (true)
open import Data.Unit using (tt)
open import Data.List using ([]; [_])

open import Arch using (ArchInfo)

module Safety (info : ArchInfo) where

open import System info

-- A value of type Steps p contains a successor for p, as well as a proof of succession
Steps : Process → Set
Steps p₀ = Σ Process (λ p₁ → p₀ ↝ p₁)

-- For every well typed process, that process is either in the halted state or can step again
progress : {p : Process} → SafeProcess p → Steps p ⊎ Halted p
progress (typed-halted halted) = inj₂ halted
progress {p} (typed-machine {fall = fall} live htC rtC disas safe-code-halt) =
  let p' : Process
      p' = record p { halted = true; pc = fall }
  in inj₁ (p' , ↝-fall live disas (↝-halted tt ↝-halt))

-- For every well typed process, taking a step results in a new well typed process
preservation : {p₀ p₁ : Process} → SafeProcess p₀ → p₀ ↝ p₁ → SafeProcess p₁
-- If it's halted, there's no way to construct a step
preservation (typed-halted halted) step with (live-step step) halted
... | ()
preservation (typed-machine _ _ _ disas safe-code-halt) (↝-fall _ disas' ↝-done) = {!!}
preservation (typed-machine live htC rtC disas safe-code-halt) (↝-fall x x₁ (↝-halted halted _)) = typed-halted halted
preservation (typed-machine live htC rtC disas safe-code-halt) (↝-fall x x₁ (↝-step x₃ x₄)) = typed-halted {!!}
preservation (typed-machine live htC rtC disas safe-code-halt) (↝-jump _ _ steps) = typed-halted {!!}

-- If the process p₀ is well typed, and it can evolve to some future process p, then the future process has halted or can take a step.
safety : {p₀ p : Process} → SafeProcess p₀ → p₀ ↝* p → Steps p ⊎ Halted p
safety typing trans = progress (↝*-transport preservation typing trans)
