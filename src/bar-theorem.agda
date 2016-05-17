module Bar-Theorem where

open import Prelude.Natural
open import Prelude.Monoidal hiding (_⇒_)
open import Prelude.Path
open import Prelude.Finite

import Dialogue as 𝓓
open import Baire
open import Securability
open import System-T.Syntax
open import System-T.Semantics

_[_]↦_ : Point → Nat → Nat → Point
(α [ i ]↦ x) j with i Nat.≟ j
(α [ i ]↦ x) j | ⊕.inl no = α j
(α [ i ]↦ x) .i | ⊕.inr refl = x

module BarTheorem (φ : Species) (φ-mono : monotone φ) where
  open Π using (_∘_)

  bar-theorem
    : (F : ⊢ᵀ (` nat ⇒ ` nat) ⇒ (` nat))
    → F ⊩ᵀ φ bar
    → ⊨ φ bar
  bar-theorem F =
    analyze [] 𝓑.⟦ F · Ω ⟧₀
      ∘ lemma F

    where
      lemma
        : (F : ⊢ᵀ (` nat ⇒ ` nat) ⇒ (` nat))
        → F ⊩ᵀ φ bar
        → 𝓑.⟦ F · Ω ⟧₀ ⊩ φ bar
      lemma F p α rewrite coherence α F =
        p α

      0⋯ : Point
      0⋯ _ = 0

      analyze
        : (U : Neigh)
        → (𝓭 : 𝓓.𝓑 Nat)
        → 𝓭 ⊩ U ◃ φ
        → ⊨ U ◃ φ
      analyze [] (𝓓.η ze) f =
        η f 0⋯
      analyze (U ⌢ x) (𝓓.η ze) f =
        η ≡.coe* φ (Point.⊢.prepend-take-len _) (f 0⋯)
      analyze U (𝓓.η (su n)) f =
        ϝ λ x →
          analyze (U ⌢ x) (𝓓.η n)
            (≡.coe* φ
               (Point.⊢.take-cong
                  (Point.⊢.su-+-transpose _ n)
                  (λ _ → refl))
               ∘ f
               ∘ x ∷_)

      analyze [] (𝓓.ϝ ze κ) f =
        ϝ λ x →
          analyze ([] ⌢ x) (κ x) λ α →
            let g = f (x ∷ α)
            in {!!} -- clearly true by φ-mono

      analyze [] (𝓓.ϝ (su_ i) κ) f =
        ϝ λ x →
          analyze ([] ⌢ x) (𝓓.ϝ i κ) λ α →
            let
              goal : φ ((x ∷ α) [ 𝓓.⟦ κ ((x ∷ α) i) ⟧ (x ∷ α) Nat.+ 1 ])
              goal = {!!}

              g : φ ((x ∷ α) [ 𝓓.⟦ κ (α i) ⟧ (x ∷ α) Nat.+ 0 ])
              g = f (x ∷ α)
            in {!!}

      -- each ϝ 0 case will be true, but the trick is to
      -- get the induction to go; we are now in a position to
      -- prefer to work with cons-lists, but we wanted snoc lists
      -- for the earlier cases.
      analyze ([] ⌢ x) (𝓓.ϝ ze κ) f =
        analyze ([] ⌢ x) (κ x) f

      analyze (U ⌢ x ⌢ x₁) (𝓓.ϝ ze κ) f = {!!}
      -- ...

      analyze (U ⌢ x) (𝓓.ϝ (su_ i) κ) f =
        {!!}
