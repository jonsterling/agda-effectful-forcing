module Dialogue where

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
  η : Z → 𝓓 Y Z
  ϝ : (Y → 𝓓 Y Z) → 𝓓 Y Z

eval[_] : {Y Z : Set} → 𝓓 Y Z → Y ^ω → Z
eval[ η x ] α = x
eval[ ϝ 𝓭[_] ] α = eval[ 𝓭[ α 0 ] ] (α ∘ su_)

𝓓[_] : {Y Z : Set} → 𝓓 Y Z → Y ^ω → Z
𝓓[_] = eval[_]

{-# DISPLAY eval[_] 𝔡 α = 𝓓[ 𝔡 ] α #-}
