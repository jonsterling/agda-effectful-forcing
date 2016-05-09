module Dialogue where

open import Prelude.Monoidal
open import Prelude.Path

-- A dialogue tree is precisely Brouwer's notion of a "mental construction"
-- of a functional on the points of a spread.
data 𝔇 (X Y Z : Set) : Set where
  η : Z → 𝔇 X Y Z
  ϝ : (Y → 𝔇 X Y Z) → X → 𝔇 X Y Z

-- A dialogue tree can be executed.
𝔇[_] : {X Y Z : Set} → 𝔇 X Y Z → (X → Y) → Z
𝔇[ η z ] α = z
𝔇[ ϝ φ x ] α = 𝔇[ φ (α x) ] α

-- A functional is called «eloquent» if it can be coded as a dialogue tree.
eloquent : {X Y Z : Set} → ((X → Y) → Z) → Set
eloquent f = Σ[ _ ∋ δ ] ∀ α → 𝔇[ δ ] α ≡ f α
