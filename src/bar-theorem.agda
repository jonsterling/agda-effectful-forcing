module Bar-Theorem where

open import Prelude.Natural
open import Prelude.Monoidal hiding (_⇒_)
open import Prelude.Path

import Dialogue as 𝓓
open import Baire
open import Securability
open import System-T.Syntax
open import System-T.Semantics

module BarTheorem (φ : Species) (φ-mono : monotone φ) where
  open Π using (_∘_)

  bar-theorem
    : (F : ⊢ᵀ (` nat ⇒ ` nat) ⇒ (` nat))
    → F ⊩ᵀ φ bar
    → ⊨ φ bar
  bar-theorem F =
    analyze [] (𝓓.sort₀ 𝓑.⟦ F · Ω ⟧₀)
      ∘ lemma F

    where
      lemma
        : (F : ⊢ᵀ (` nat ⇒ ` nat) ⇒ (` nat))
        → F ⊩ᵀ φ bar
        → 𝓓.sort₀ 𝓑.⟦ F · Ω ⟧₀ ⊩ φ bar
      lemma F p α rewrite 𝓓.coherence 𝓑.⟦ F · Ω ⟧₀ α ≡.⁻¹ | interpretation-correct α F =
        p α

      0⋯ : Point
      0⋯ _ = 0

      analyze
        : (U : Neigh) (𝓭 : 𝓓.𝓑ₙ Nat)
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
      analyze U (𝓓.ϝ κ) f =
        ϝ λ x →
          analyze (U ⌢ x) (κ x) λ α →
            ≡.coe*
              (λ n → φ ((U ⊕< x ∷ α) [ n ]))
              (Point.⊢.su-+-transpose _ (𝓓.⟦ κ x ⟧ₙ α))
              (φ-mono (f (x ∷ α)))

