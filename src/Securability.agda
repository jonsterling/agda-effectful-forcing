{-# OPTIONS --without-K #-}

module Securability where

open import Basis

open import Spread.Baire
open import Dialogue as 𝓓
open import SystemT.Syntax
open import SystemT.Semantics

infixl 4 _◂_

-- A Brouwerian mental construction to verify that a node is securable.
data _◂_ (U : Node) (φ : Species) : Set where
  spit : φ U → U ◂ φ
  bite : (∀ x → U ⌢ x ◂ φ) → U ◂ φ

-- Proof that a dialogue computes the securability of a node.
_⊩_◃_
  : 𝔅 ℕ ℕ
  → Node
  → Species
  → Set
d ⊩ U ◃ φ =
  (α : Point)
    → φ (U <++ α [ 𝔅[ d ⋄ α ] + ∣ U ∣ ])

_⊩_◃ᵀ_
  : ⊢ᵀ (nat ⇒ nat) ⇒ nat
  → Node
  → Species
  → Set
F ⊩ U ◃ᵀ φ =
  (α : Point)
    → φ (U <++ α [ tm⟦ F ⟧₀ α + ∣ U ∣ ])
