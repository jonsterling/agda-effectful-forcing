module Snoc where

open import Prelude.List

snoc : {X : Set} → List X → X → List X
snoc [] x = x ∷ []
snoc (x ∷ U) y = x ∷ (snoc U y)

module SL where
  data View {X : Set} : List X → Set where
    [] : View []
    _⌢_ : (U : List X) (x : X) → View (snoc U x)

  view : {X : Set} → (U : List X) → View U
  view [] = []
  view (x ∷ U) with view U
  view (x ∷ .[]) | [] = [] ⌢ x
  view (x ∷ ._) | U ⌢ y = (x ∷ U) ⌢ y

_⌢_ : {X : Set} → List X → X → List X
U ⌢ x = snoc U x
{-# DISPLAY snoc U x = U ⌢ x #-}
