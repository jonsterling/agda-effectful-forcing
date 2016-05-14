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
    → δ ⊨ U ◃ φ -- I have a nagging suspicion that the definition of this premise is wrong.
    → ⊢ U ◃ φ

  -- The initial node is secured 0 steps in any direction: we are in the bar.
  bar-theorem [] (η ze) f =
    η (f 0⋯)

  -- The initial node is secured n+1 steps in any direction: we apply the ϝ
  -- rule n times to reach the bar.
  bar-theorem [] (η (su_ n)) f =
    ϝ λ x →
      bar-theorem _ (η n) {!!}

  -- An m+1-node is secured 0 steps in any direction: we have already been in the bar
  -- for n steps, and must retrace our steps.
  bar-theorem (U ⌢ x) (η ze) f =
    ζ (bar-theorem U (η ze) f)

  -- An m+1 node is secured n steps in any direction: I have no idea what to do.
  bar-theorem (U ⌢ x) (η (su_ n)) f =
    let
      ih = bar-theorem U (η n) {!!}
    in {!!}

  bar-theorem U (ϝ κ) f =
    ϝ λ x →
      bar-theorem
        (U ⌢ x)
        (κ x)
        (≡.coe* φ {!!}
           ∘ f
           ∘ cons x)
