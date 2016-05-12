module Brouwer where

open import Prelude.List
open import Prelude.Natural

open import Snoc
open import Dialogue
open import Baire

data ⊢_◃_ : (U : List Nat) (φ : List Nat → Set) → Set where
  η : ∀ {φ U} → φ U → ⊢ U ◃ φ
  ζ : ∀ {φ U x} → ⊢ U ◃ φ → ⊢ U ⌢ x ◃ φ
  ϝ : ∀ {φ U} → (∀ x → ⊢ U ⌢ x ◃ φ) → ⊢ U ◃ φ

⊢_bar : (List Nat → Set) → Set
⊢ φ bar = ⊢ [] ◃ φ

data ⊩_◃_ : (U : List Nat) (φ : List Nat → Set) → Set where
  η : ∀ {φ U} → φ U → ⊩ U ◃ φ
  ϝ : ∀ {φ U} → (∀ x → ⊩ U ⌢ x ◃ φ) → ⊩ U ◃ φ

⊩_bar : (List Nat → Set) → Set
⊩ φ bar = ⊩ [] ◃ φ

monotone : (φ : List Nat → Set) → Set
monotone φ = ∀ {U x} → φ U → φ (U ⌢ x)

-- Following Brouwer's argument, we can normalize any monotone bar to remove the
-- ζ inferences, which are really just embedded appeals to monotonicity.
module Normalize {φ : List Nat → Set} (φ-mono : monotone φ) where
  ⊩-mono : monotone (⊩_◃ φ)
  ⊩-mono (η x) = η (φ-mono x)
  ⊩-mono (ϝ κ) = ϝ λ x → ⊩-mono (κ _)

  eval : ∀ {U} → ⊢ U ◃ φ → ⊩ U ◃ φ
  eval (η x) = η x
  eval (ζ p) = ⊩-mono (eval p)
  eval (ϝ κ) = ϝ (λ x → eval (κ x))

  quo : ∀ {U} → ⊩ U ◃ φ → ⊢ U ◃ φ
  quo (η x) = η x
  quo (ϝ κ) = ϝ λ x → quo (κ x)

  norm : ∀ {U} → ⊢ U ◃ φ → ⊢ U ◃ φ
  norm x = quo (eval x)

-- δ ⊨ U ◃ φ means that δ computes the securability of U by φ.
_⊨_◃_ : 𝔅ₙ Nat → List Nat → (List Nat → Set) → Set
δ ⊨ U ◃ φ =
  (α : Point)
    → φ (take (𝔇ₙ[ δ ] α) (U ⊕< α))

_⊨_bar : 𝔅ₙ Nat → (List Nat → Set) → Set
δ ⊨ φ bar = δ ⊨ [] ◃ φ
