module Dialogue where

open import Prelude.Functor
open import Prelude.Monad
open import Prelude.Natural
open import Prelude.Monoidal

open Π using (_∘_)

Seq : Set → Set
Seq X = Nat → X

_^ω : Set → Set
X ^ω = Seq X

{-# DISPLAY Seq X = X ^ω #-}

-- A dialogue tree is precisely Brouwer's notion of a "mental construction"
-- of a functional on the points of a spread.
data 𝓓 (Y Z : Set) : Set where
  η_ : Z → 𝓓 Y Z
  ϝ : (Y → 𝓓 Y Z) → 𝓓 Y Z

eval : {Y Z : Set} → 𝓓 Y Z → Y ^ω → Z
eval (η x) α = x
eval (ϝ 𝓭[_]) α = eval (𝓭[ α 0 ]) (α ∘ su_)

⟦_⟧ : {Y Z : Set} → 𝓓 Y Z → Y ^ω → Z
⟦_⟧ = eval

{-# DISPLAY eval 𝓭 α = ⟦ 𝓭 ⟧ α #-}

-- A mental construction of a functional on the Baire space
𝓑 : Set → Set
𝓑 = 𝓓 Nat

instance
  𝓓-functor : ∀ {X} → Functor (𝓓 X)
  Functor.map 𝓓-functor f (η x) = η (f x)
  Functor.map 𝓓-functor f (ϝ 𝓭[_]) = ϝ λ x → map f 𝓭[ x ]

  𝓓-monad : ∀ {X} → Monad (𝓓 X)
  Monad.return_ 𝓓-monad = η_
  Monad.bind 𝓓-monad κ (η x) = κ x
  Monad.bind 𝓓-monad κ (ϝ 𝓭[_]) = ϝ λ x → Monad.bind 𝓓-monad κ 𝓭[ x ]
