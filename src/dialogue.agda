module Dialogue where

open import Prelude.Monoidal
open import Prelude.Path

data 𝔇 (X Y Z : Set) : Set where
  η : Z → 𝔇 X Y Z
  ϝ : (Y → 𝔇 X Y Z) → X → 𝔇 X Y Z

𝔇[_] : {X Y Z : Set} → 𝔇 X Y Z → (X → Y) → Z
𝔇[ η z ] α = z
𝔇[ ϝ φ x ] α = 𝔇[ φ (α x) ] α

eloquent : {X Y Z : Set} → ((X → Y) → Z) → Set
eloquent f = Σ[ _ ∋ δ ] ∀ α → 𝔇[ δ ] α ≡ f α
