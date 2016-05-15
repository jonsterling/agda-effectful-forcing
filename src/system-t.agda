module System-T where

open import Prelude.Finite
open import Prelude.Natural
open import Prelude.List
open import Prelude.Monoidal hiding (_⇒_)
import Prelude.Inspect as I
open import Prelude.Maybe
open import Prelude.Path
open import Prelude.Decidable

open import Baire hiding (take; _⊕<_)
open import Brouwer
open import Dialogue
open import Context

open import System-T.Syntax
open import System-T.Semantics

module BarTheorem (φ : Species) (mono : monotone φ) where
  open Normalize {φ} mono
  open Π using (_∘_)
  open Nat using (_+_)

  0⋯ : Point
  0⋯ _ = 0

  ⌢-cong : ∀ {U V : Neigh} {x y} → U ≡ V → x ≡ y → U ⌢ x ≡ V ⌢ y
  ⌢-cong refl refl = refl

  nth-cong : ∀ (α β : Point) {i j : Nat} → α ≈ β → i ≡ j → α i ≡ β j
  nth-cong α β h refl = h _

  su-+-transpose : ∀ m n → su (n + m) ≡ n + su m
  su-+-transpose ze ze = refl
  su-+-transpose ze (su_ n) rewrite su-+-transpose ze n = refl
  su-+-transpose (su m) ze = refl
  su-+-transpose (su m) (su_ n) rewrite su-+-transpose (su m) n = refl

  prepend-+-len : ∀ U n {α} → (U ⊕< α) (n + len U) ≡ α n
  prepend-+-len [] n rewrite Nat.⊢.ρ⇒ {n} = refl
  prepend-+-len (U ⌢ x) n {α} =
    prepend-+-len U (su n) {cons x α} ≡.⟔
      nth-cong
        (U ⌢ x ⊕< α)
        (U ⌢ x ⊕< α)
        (λ i → refl)
        (su-+-transpose (len U) n ≡.⁻¹)

  prepend-take-len : ∀ U {α} → take (len U) (U ⊕< α) ≡ U
  prepend-take-len [] = refl
  prepend-take-len (U ⌢ x) = ⌢-cong (prepend-take-len U) (prepend-+-len U 0)


  bar-theorem
    : ∀ U δ
    → δ ⊨ U ◃ φ
    → ⊢ U ◃ φ

  bar-theorem [] (η ze) f =
    η (f 0⋯)

  bar-theorem (U ⌢ x) (η ze) f =
    η (≡.coe* φ (prepend-take-len _) (f 0⋯))

  bar-theorem U (η (su_ n)) f =
    ϝ λ x →
      bar-theorem (U ⌢ x) (η n)
        (≡.coe* φ
           (take-cong _ _
              (su-+-transpose _ n)
              (λ _ → refl))
           ∘ f
           ∘ cons x)

  bar-theorem U (ϝ κ) f =
    ϝ λ x →
      bar-theorem (U ⌢ x) (κ x) λ α →
        ≡.coe*
          (λ n → φ (take n (U ⊕< cons x α)))
          (su-+-transpose _ (𝔇ₙ[ κ x ] α))
          (mono (f (cons x α)))
