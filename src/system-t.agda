module System-T where

open import Prelude.Natural
open import Prelude.Monoidal hiding (_⇒_)
import Prelude.Inspect as I
open import Prelude.Maybe
open import Prelude.Path
open import Prelude.Decidable

open import Baire
open import Securability
import Dialogue as 𝓓

module BarTheorem (φ : Species) (φ-mono : monotone φ) where
  open Π using (_∘_)

  0⋯ : Point
  0⋯ _ = 0

  bar-theorem
    : ∀ U δ
    → δ ⊩ U ◃ φ
    → ⊨ U ◃ φ

  bar-theorem [] (𝓓.η ze) f =
    η f 0⋯

  bar-theorem (U ⌢ x) (𝓓.η ze) f =
    η ≡.coe* φ (Point.⊢.prepend-take-len _) (f 0⋯)

  bar-theorem U (𝓓.η (su n)) f =
    ϝ λ x →
      bar-theorem (U ⌢ x) (𝓓.η n)
        (≡.coe* φ
           (Point.⊢.take-cong
              (Point.⊢.su-+-transpose _ n)
              (λ _ → refl))
           ∘ f
           ∘ x ∷_)

  bar-theorem U (𝓓.ϝ κ) f =
    ϝ λ x →
      bar-theorem (U ⌢ x) (κ x) λ α →
        ≡.coe*
          (λ n → φ ((U ⊕< x ∷ α) [ n ]))
          (Point.⊢.su-+-transpose _ (𝓓.⟦ κ x ⟧ α))
          (φ-mono (f (x ∷ α)))
