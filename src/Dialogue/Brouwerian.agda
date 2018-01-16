module Dialogue.Brouwerian where

open import Basis

import Dialogue.Core as Core
open Core hiding (module ⊢)

-- In the normalized (Brouwerian) version of the dialogue tree, queries are
-- given in order.
data 𝔅 (Y Z : Set) : Set where
  -- η x means that the result is x.
  η_
    : Z
    → 𝔅 Y Z

  -- ϝ 𝓭[_] means that we request the *current* element x of the choice sequence
  -- and proceed with 𝓭[x].
  ϝ
    : (Y → 𝔅 Y Z)
    → 𝔅 Y Z


-- A dialogue may be run against a choice sequence.
_$ₙ_ : {Y Z : Set} → 𝔅 Y Z → (Nat → Y) → Z
(η x) $ₙ α = x
ϝ 𝓭[_] $ₙ α = 𝓭[ α 0 ] $ₙ (α ∘ suc)
