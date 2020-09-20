{-# OPTIONS --without-K #-}

module BarTheorem where

open import Basis
open import Spread.Baire
open import Securability
open import SystemT.Syntax
import SystemT.Context as Ctx

import Dialogue as 𝓓
import SystemT.Semantics as Sem

open Sem
open 𝓓 hiding (module ⊢)

module BarTheorem (𝔅 : Species) (𝔅-mono : monotone 𝔅) where

  -- The content of Brouwer's Bar Theorem is that if we have a functional that
  -- will compute for any point α the length of the first approximation U ≺ α
  -- that is in the species φ, then we can well-order this insight into a
  -- mental construction that φ is a bar.
  bar-theorem
    : (F : ⊢ᵀ (nat ⇒ nat) ⇒ nat)
    → F ⊩ [] ◃ᵀ 𝔅
    → [] ◂ 𝔅
  bar-theorem F =
    analyze [] (𝓓.norm (tm⟪ F ⟫₀ 𝓓.generic))
      ∘ lemma F

    where
      lemma
        : (F : ⊢ᵀ (nat ⇒ nat) ⇒ nat)
        → F ⊩ [] ◃ᵀ 𝔅
        → 𝓓.norm (tm⟪ F ⟫₀ 𝓓.generic) ⊩ [] ◃ 𝔅
      lemma F p α =
        ≡.coe*
         (λ ■ → 𝔅 (α [ ■ + 0 ]))
         (≡.seq
          (Coh.soundness₀ _ F _ generic λ ⟦n⟧ ⟪n⟫ ⟦n⟧∼⟪n⟫ →
           ≡.seq
            (≡.cong α ⟦n⟧∼⟪n⟫)
            (𝓓.⊢.generic-diagram α ⟪n⟫))
          (𝓓.⊢.coh (tm⟪ F ⟫₀ generic) α))
         (p α)

      0⋯ : Point
      0⋯ _ = 0

      analyze
        : (U : Node)
        → (𝓭 : 𝓓.𝔅 Nat Nat)
        → 𝓭 ⊩ U ◃ 𝔅
        → U ◂ 𝔅

      analyze U (η zero) f =
        η ≡.coe* 𝔅 (Point.⊢.prepend-take-len U) (f 0⋯)

      analyze U (η (suc n)) f =
        ϝ λ x →
        analyze _ (𝓓.η n) λ α →
        ≡.coe* 𝔅
         (Point.⊢.take-cong
          (Point.⊢.su-+-transpose ∣ U ∣ n)
          (λ _ → refl))
         (f (x <∷ α))

      analyze U (ϝ κ) f =
        ϝ λ x →
        analyze (U ⌢ x) (κ x) λ α →
          ≡.coe*
            (λ ■ → 𝔅 ((U <++ x <∷ α) [ ■ ]))
            (Point.⊢.su-+-transpose _ 𝔅[ κ x ⋄ α ])
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

      relabel U (ϝ m) =
        𝔄-hered λ x →
        relabel (U ⌢ x) (m x)


      induction
        : (F : ⊢ᵀ (nat ⇒ nat) ⇒ nat)
        → F ⊩ [] ◃ᵀ 𝔅
        → 𝔄 []
      induction F =
        relabel []
        ∘ bar-theorem F
