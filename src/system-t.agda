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


  -- The following should hold; if it does not, then we have got the
  -- wrong definitions!
  ⊨-mono : ∀ δ U x → δ ⊨ U ◃ φ → δ ⊨ U ⌢ x ◃ φ
  ⊨-mono (η n) U x f α = f (cons x α)
  ⊨-mono (ϝ κ) U x f α = {!!}

  -- I don't know if the following two lemmas should be true, but they
  -- seem to be needed.
  lemma1 : ∀ U n x → η (su n) ⊨ U ⌢ x ◃ φ → η n ⊨ U ◃ φ
  lemma1 [] ze x f = {!!}
  lemma1 [] (su_ n) x f = {!!}
  lemma1 (U ⌢ y) n x = {!!}

  lemma2 : ∀ U n x → η (su n) ⊨ U ◃ φ → η n ⊨ U ⌢ x ◃ φ
  lemma2 [] ze x f = {!!} -- true
  lemma2 [] (su_ n) x f = {!!}
  lemma2 (U ⌢ y) n x f = {!!}

  bar-theorem
    : ∀ U δ
    → δ ⊨ U ◃ φ -- I have a nagging suspicion that the definition of this premise is wrong.
    → ⊢ U ◃ φ

  -- The initial node is secured 0 steps in any direction: we are in the bar.
  bar-theorem [] (η ze) f = -- GOOD TO GO
    η (f 0⋯)

  -- An m+1-node is secured 0 steps in any direction: we have already been in the bar
  -- for n steps, and must retrace our steps.
  bar-theorem (U ⌢ x) (η ze) f = -- GOOD TO GO
    ζ (bar-theorem U (η ze) f)

  -- The initial node is secured n+1 steps in any direction: we apply the ϝ
  -- rule n times to reach the bar.
  bar-theorem [] (η (su_ n)) f =
    ϝ λ x →
      bar-theorem _ (η n) (lemma2 [] n x f)

  -- An m+1 node is secured n steps in any direction: I have no idea what to do.
  bar-theorem (U ⌢ x) (η (su_ n)) f =
    ζ (bar-theorem U (η n) (lemma1 U n x f))

  bar-theorem U (ϝ κ) f = -- GOOD TO GO
    ϝ λ x →
      bar-theorem
        (U ⌢ x)
        (κ x)
        (f ∘ cons x)
