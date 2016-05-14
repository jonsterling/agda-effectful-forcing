module Brouwer where

open import Prelude.List
open import Prelude.Natural
open import Prelude.Monoidal
open import Prelude.Path
open import Prelude.Functor

open import Dialogue
open import Baire hiding (_⊕<_; prepend; take)

data SnocList (X : Set) : Set where
  [] : SnocList X
  _⌢_ : SnocList X → X → SnocList X

len : {X : Set} → SnocList X → Nat
len [] = 0
len (U ⌢ x) = su (len U)

Neigh : Set
Neigh = SnocList Nat

Species : Set₁
Species = Neigh → Set

data ⊢_◃_ : (U : Neigh) (φ : Species) → Set where
  η : ∀ {φ U} → φ U → ⊢ U ◃ φ
  ζ : ∀ {φ U x} → ⊢ U ◃ φ → ⊢ U ⌢ x ◃ φ
  ϝ : ∀ {φ U} → (∀ x → ⊢ U ⌢ x ◃ φ) → ⊢ U ◃ φ

⊢_bar : (Neigh → Set) → Set
⊢ φ bar = ⊢ [] ◃ φ

data ⊩_◃_ : (U : Neigh) (φ : Species) → Set where
  η : ∀ {φ U} → φ U → ⊩ U ◃ φ
  ϝ : ∀ {φ U} → (∀ x → ⊩ U ⌢ x ◃ φ) → ⊩ U ◃ φ

⊩_bar : Species → Set
⊩ φ bar = ⊩ [] ◃ φ

monotone : Species → Set
monotone φ = ∀ {U x} → φ U → φ (U ⌢ x)

-- Following Brouwer's argument, we can normalize any monotone bar to remove the
-- ζ inferences, which are really just embedded appeals to monotonicity.
module Normalize {φ : Species} (φ-mono : monotone φ) where
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

open Nat using (_+_; _-_)
open List using (_++_)

prepend : Neigh → Point → Point
prepend [] α i = α i
prepend (U ⌢ x) α = prepend U (cons x α)

_⊕<_ : Neigh → Point → Point
U ⊕< α = prepend U α

{-# DISPLAY prepend U α = U ⊕< α #-}

take : Nat → Point → Neigh
take ze α = []
take (su n) α = (take n α) ⌢ (α n)

_⊨_◃_ : 𝔅ₙ Nat → Neigh → Species → Set
δ ⊨ U ◃ φ =
  (α : Point)
    → φ (take (𝔇ₙ[ δ ] α) (U ⊕< α))

-- δ ⊨ U ◃ φ means that δ computes the securability of U by φ.
_⊨_bar : 𝔅ₙ Nat → Species → Set
δ ⊨ φ bar =
  δ ⊨ [] ◃ φ

module _ {φ : Species} (φ-mono : monotone φ) where
  soundness₁
    : ∀ U
    → ⊩ U ◃ φ
    → 𝔅ₙ Nat
  soundness₁ U (η x) =
    η (len U)
  soundness₁ U (ϝ κ) =
    ϝ λ x →
      soundness₁
        (U ⌢ x)
        (κ x)

{-
  soundness₂
    : ∀ U
    → (p : ⊩ U ◃ φ)
    → soundness₁ U p ⊨ U ◃ φ
  soundness₂ U (η p) α rewrite take-len-prepend U α = p
  soundness₂ U (ϝ κ) α =
    ≡.coe* φ
      (take-snoc-tail-law U α n ≡.⁻¹)
      (soundness₂ (U ⌢ α 0) (κ (α 0)) (tail α))
    where
      δ = soundness₁ (U ⌢ α 0) (κ (α 0))
      n = 𝔇ₙ[ δ ] (tail α)

  soundness
    : ∀ {U}
    → ⊩ U ◃ φ
    → Σ[ 𝔅ₙ Nat ∋ δ ] δ ⊨ U ◃ φ
  soundness p =
    soundness₁ _ p
      ▸ soundness₂ _ p

-}
