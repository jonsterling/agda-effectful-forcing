module BarTheorem where

open import Basis

import Dialogue as 𝓓
open import Spread.Baire
open import Securability
open import SystemT.Syntax
import SystemT.Semantics as Sem
open Sem hiding (module ⊢)

module BarTheorem (𝔅 : Species) (𝔅-mono : monotone 𝔅) where

  ζ[_] : ∀ {U} x → U ◂ 𝔅 → U ⌢ x ◂ 𝔅
  ζ[ x ] (η y) = η 𝔅-mono y
  ζ[ x ] (ϝ 𝓭[_]) = 𝓭[ x ]

  -- The content of Brouwer's Bar Theorem is that if we have a functional that
  -- will compute for any point α the length of the first approximation U ≺ α
  -- that is in the species φ, then we can well-order this insight into a
  -- mental construction that φ is a bar.
  bar-theorem
    : (F : ⊢ᵀ (` nat ⇒ ` nat) ⇒ (` nat))
    → F ⊩ [] ◃ᵀ 𝔅
    → [] ◂ 𝔅
  bar-theorem F =
    analyze [] (𝓓.norm (𝓑.⟦ F ⟧₀ 𝓓.generic))
      ∘ lemma F

    where
      lemma
        : (F : ⊢ᵀ (` nat ⇒ ` nat) ⇒ (` nat))
        → F ⊩ [] ◃ᵀ 𝔅
        → 𝓓.norm (𝓑.⟦ F ⟧₀ 𝓓.generic) ⊩ [] ◃ 𝔅
      lemma F p α
        rewrite
            𝓓.⊢.coh (𝓑.⟦ F ⟧₀ 𝓓.generic) α ≡.⁻¹
          | Sem.⊢.soundness α F {_} {𝓑.𝒢.⋄} (λ ()) α 𝓓.generic (λ _ 𝓮 f → 𝓓.⊢.generic-diagram α 𝓮 ≡.▪ ≡.ap¹ α f) ≡.⁻¹
          = p α

      0⋯ : Point
      0⋯ _ = 0

      analyze
        : (U : Node)
        → (𝓭 : 𝓓.𝔅 Nat Nat)
        → 𝓭 ⊩ U ◃ 𝔅
        → U ◂ 𝔅

      analyze U (𝓓.η zero) f =
        η ≡.coe* 𝔅 (Point.⊢.prepend-take-len U) (f 0⋯)

      analyze U (𝓓.η (suc n)) f =
        ϝ λ x →
          analyze (U ⌢ x) (𝓓.η n)
            (≡.coe* 𝔅 (Point.⊢.take-cong (Point.⊢.su-+-transpose ∣ U ∣ n) λ _ → refl)
               ∘ f
               ∘ (x <∷_))

      analyze U (𝓓.ϝ κ) f =
        ϝ λ x →
          analyze (U ⌢ x) (κ x) λ α →
            ≡.coe*
              (λ n → 𝔅 ((U <++ x <∷ α) [ n ]))
              (Point.⊢.su-+-transpose _ (κ x 𝓓.$ₙ α))
              (𝔅-mono (f (x <∷ α)))


  -- The Bar Induction Principle is a corollary to the Bar Theorem.
  module Induction
    (𝔄 : Species)
    (𝔅⊑𝔄 : 𝔅 ⊑ 𝔄)
    (𝔄-hered : hereditary 𝔄)
    where

      relabel
        : (U : Node)
        → (U ◂ 𝔅)
        → 𝔄 U

      relabel U (η x) =
        𝔅⊑𝔄 U x

      relabel U (ϝ 𝓭[_]) =
        𝔄-hered λ x →
          relabel (U ⌢ x) 𝓭[ x ]


      induction
        : (F : ⊢ᵀ (` nat ⇒ ` nat) ⇒ (` nat))
        → F ⊩ [] ◃ᵀ 𝔅
        → 𝔄 []
      induction F =
        relabel []
          ∘ bar-theorem F