module Securability where

open import Prelude.Natural

open import Spread.Baire
open import Dialogue as 𝓓
open import SystemT.Syntax
open import SystemT.Semantics

infixl 4 _◂_

-- A Brouwerian mental construction to verify that a node is securable.
data _◂_ (U : Neigh) (φ : Species) : Set where
  η_ : φ U → U ◂ φ
  ϝ : (∀ x → U ⌢ x ◂ φ) → U ◂ φ

open Nat using (_+_; _-_)

-- Proof that a dialogue computes the securability of a node.
_⊩_◃_
  : 𝔅 Nat Nat
  → Neigh
  → Species
  → Set
𝓭 ⊩ U ◃ φ =
  (α : Point)
    → φ (U ⨭ α [ 𝓭 𝓓.$ₙ α + ∣ U ∣ ])

_⊩_◃ᵀ_
  : ⊢ᵀ (` nat ⇒ ` nat) ⇒ ` nat
  → Neigh
  → Species
  → Set
F ⊩ U ◃ᵀ φ =
  (α : Point)
    → φ (U ⨭ α [ T.⟦ F ⟧₀ α + ∣ U ∣ ])
