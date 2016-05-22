module BarTheorem where

open import Prelude.Natural
open import Prelude.Monoidal hiding (_⇒_)
open import Prelude.Path

import Dialogue as 𝓓
open import Spread.Baire
open import Securability
open import SystemT.Syntax
import SystemT.Semantics as Sem
open Sem hiding (module ⊢)

module BarTheorem (𝔅 : Species) (𝔅-mono : monotone 𝔅) where
  open Π using (_∘_)

  ζ[_] : ∀ {U} x → ⊨ U ◃ 𝔅 → ⊨ U ⌢ x ◃ 𝔅
  ζ[ x ] (η y) = η 𝔅-mono y
  ζ[ x ] (ϝ 𝓭[_]) = 𝓭[ x ]

  -- The content of Brouwer's Bar Theorem is that if we have a functional that
  -- will compute for any point α the length of the first approximation U ≺ α
  -- that is in the species φ, then we can well-order this insight into a
  -- mental construction that φ is a bar.
  bar-theorem
    : (F : ⊢ᵀ (` nat ⇒ ` nat) ⇒ (` nat))
    → F ⊩ᵀ 𝔅 bar
    → ⊨ 𝔅 bar
  bar-theorem F =
    analyze [] (𝓓.norm 𝓑.⟦ F · Ω ⟧₀)
      ∘ lemma F

    where
      lemma
        : (F : ⊢ᵀ (` nat ⇒ ` nat) ⇒ (` nat))
        → F ⊩ᵀ 𝔅 bar
        → 𝓓.norm 𝓑.⟦ F · Ω ⟧₀ ⊩ 𝔅 bar
      lemma F p α
        rewrite
            𝓓.⊢.coh 𝓑.⟦ F · Ω ⟧₀ α ≡.⁻¹
          | Sem.⊢.soundness₀ (F · Ω) α ≡.⁻¹ = p α


      0⋯ : Point
      0⋯ _ = 0

      analyze
        : (U : Neigh)
        → (𝓭 : 𝓓.𝓑ₙ Nat)
        → 𝓭 ⊩ U ◃ 𝔅
        → ⊨ U ◃ 𝔅

      analyze U (𝓓.η ze) f =
        η ≡.coe* 𝔅 (Point.⊢.prepend-take-len U) (f 0⋯)

      analyze U (𝓓.η (su n)) f =
        ϝ λ x →
          analyze (U ⌢ x) (𝓓.η n)
            (≡.coe* 𝔅 (Point.⊢.take-cong (Point.⊢.su-+-transpose ∣ U ∣ n) λ _ → refl)
               ∘ f
               ∘ x ∷_)

      analyze U (𝓓.ϝ κ) f =
        ϝ λ x →
          analyze (U ⌢ x) (κ x) λ α →
            ≡.coe*
              (λ n → 𝔅 ((U ⊕< x ∷ α) [ n ]))
              (Point.⊢.su-+-transpose _ (κ x 𝓓.$ₙ α))
              (𝔅-mono (f (x ∷ α)))


  -- The Bar Induction Principle is a corollary to the Bar Theorem.
  module Induction
    (𝔄 : Species)
    (𝔅⊑𝔄 : 𝔅 ⊑ 𝔄)
    (𝔄-hered : hereditary 𝔄)
    where

      relabel
        : (U : Neigh)
        → (⊨ U ◃ 𝔅)
        → 𝔄 U

      relabel U (η x) =
        𝔅⊑𝔄 U x

      relabel U (ϝ 𝓭[_]) =
        𝔄-hered λ x →
          relabel (U ⌢ x) 𝓭[ x ]


      induction
        : (F : ⊢ᵀ (` nat ⇒ ` nat) ⇒ (` nat))
        → F ⊩ᵀ 𝔅 bar
        → 𝔄 []
      induction F =
        relabel []
          ∘ bar-theorem F
