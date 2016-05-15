module Securability where

open import Prelude.Natural

open import Baire
open import Dialogue as 𝓓

data ⊨_◃_ (U : Neigh) (φ : Species) : Set where
  η_ : φ U → ⊨ U ◃ φ
  ϝ : (∀ x → ⊨ U ⌢ x ◃ φ) → ⊨ U ◃ φ

⊨_bar : Species → Set
⊨ φ bar = ⊨ [] ◃ φ

open Nat using (_+_; _-_)

_⊩_◃_
  : 𝓑 Nat
  → Neigh
  → Species
  → Set
𝓭 ⊩ U ◃ φ =
  (α : Point)
    → φ ((U ⊕< α) [ 𝓓.⟦ 𝓭 ⟧ α + ∣ U ∣ ])

-- δ ⊩ U ◃ φ means that δ computes the securability of U by φ.
_⊩_bar : 𝓑 Nat → Species → Set
𝓭 ⊩ φ bar =
  𝓭 ⊩ [] ◃ φ

{-# DISPLAY _⊩_◃_ 𝓭 [] φ = 𝓭 ⊩ φ bar #-}
{-# DISPLAY ⊨_◃_ [] φ = ⊨ φ bar #-}
