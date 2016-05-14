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

  0⋯ : Point
  0⋯ _ = 0

  bar-theorem
    : ∀ U δ
    → δ ⊨ U ◃ φ
    → ⊢ U ◃ φ

  bar-theorem [] (η ze) f =
    η (f 0⋯)

  bar-theorem [] (η (su_ n)) f =
    ϝ λ x →
      bar-theorem _ (η n) {!!}

  bar-theorem (U ⌢ x) (η ze) f =
    ζ (bar-theorem U (η ze) f)

  bar-theorem (U ⌢ x) (η (su_ n)) f =
    {!!}

    -- TODO:
    --   1. in case n > len(U), we are not yet in the bar; we must apply ϝ by (n - len(U)) times
    --   2. in case n == len(U), then we have just made it into the bar, and we apply η.
    --   3. in case n < len(U), we are already in the bar and need to apply ζ by (len(U) - n) times.
  bar-theorem U (ϝ κ) f =
    ϝ λ x →
      bar-theorem
        (U ⌢ x)
        (κ x)
        (≡.coe* φ {!!}
           ∘ f
           ∘ cons x)
