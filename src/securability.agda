module Securability where

open import Prelude.Natural

open import Baire
open import Dialogue as 𝓓
open import System-T.Syntax
open import System-T.Semantics

-- A Brouwerian mental construction to verify that a node is securable.
data ⊨_◃_ (U : Neigh) (φ : Species) : Set where
  η_ : φ U → ⊨ U ◃ φ
  ϝ : (∀ x → ⊨ U ⌢ x ◃ φ) → ⊨ U ◃ φ

open Nat using (_+_; _-_)

-- Proof that a dialogue computes the securability of a node.
_⊩_◃_
  : 𝓑ₙ Nat
  → Neigh
  → Species
  → Set
𝓭 ⊩ U ◃ φ =
  (α : Point)
    → φ ((U ⊕< α) [ 𝓭 𝓓.$ₙ α + ∣ U ∣ ])

_⊩ᵀ_◃_
  : ⊢ᵀ (` nat ⇒ ` nat) ⇒ ` nat
  → Neigh
  → Species
  → Set
F ⊩ᵀ U ◃ φ =
  (α : Point)
    → φ ((U ⊕< α) [ TΩ.⟦ F · Ω ⟧₀ α + ∣ U ∣ ])

⊨_bar
  : Species
  → Set
⊨ φ bar =
  ⊨ [] ◃ φ

_⊩_bar
  : 𝓑ₙ Nat
  → Species
  → Set
𝓭 ⊩ φ bar =
  𝓭 ⊩ [] ◃ φ

_⊩ᵀ_bar
  : ⊢ᵀ (` nat ⇒ ` nat) ⇒ ` nat
  → Species
  → Set
F ⊩ᵀ φ bar =
  F ⊩ᵀ [] ◃ φ


{-# DISPLAY _⊩_◃_ 𝓭 [] φ = 𝓭 ⊩ φ bar #-}
{-# DISPLAY _⊩ᵀ_◃_ F [] φ = F ⊩ᵀ φ bar #-}
{-# DISPLAY ⊨_◃_ [] φ = ⊨ φ bar #-}
