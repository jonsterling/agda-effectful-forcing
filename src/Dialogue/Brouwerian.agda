module Dialogue.Brouwerian where

open import Prelude.Natural
open import Prelude.Monoidal

import Dialogue.Core as Core
open Core hiding (module ⊢)

open Π using (_∘_)

-- In the normalized (Brouwerian) version of the dialogue tree, queries are
-- given in order.
data 𝓓ₙ (Y Z : Set) : Set where
  -- η x means that the result is x.
  η_
    : Z
    → 𝓓ₙ Y Z

  -- ϝ 𝓭[_] means that we request the *current* element x of the choice sequence
  -- and proceed with 𝓭[x].
  ϝ
    : (Y → 𝓓ₙ Y Z)
    → 𝓓ₙ Y Z

-- 𝓑ₙ is the type of Brouwerian mental contructions of functionals on the
-- Baire space.
𝓑ₙ : Set → Set
𝓑ₙ = 𝓓ₙ Nat

-- A dialogue may be run against a choice sequence.
_$ₙ_ : {Y Z : Set} → 𝓓ₙ Y Z → (Nat → Y) → Z
(η x) $ₙ α = x
ϝ 𝓭[_] $ₙ α = 𝓭[ α 0 ] $ₙ (α ∘ su_)
