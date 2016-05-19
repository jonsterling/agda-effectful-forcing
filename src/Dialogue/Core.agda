module Dialogue.Core where

open import Prelude.Natural
open import Prelude.Functor
open import Prelude.Monad
open import Prelude.Path

-- An Escardó dialogue, representing a functional on a space whose
-- neighborhoods are lists of Y.
data 𝓓 (X Y Z : Set) : Set where
  -- η x means that the result is x.
  η_
    : Z
    → 𝓓 X Y Z

  -- β⟨ i ⟩ 𝓭[_] means that we request the ith element x of the choice sequence
  -- and proceed with 𝓭[x].
  β⟨_⟩
    : X
    → (Y → 𝓓 X Y Z)
    → 𝓓 X Y Z

-- 𝓑 represents functionals on the Baire space.
𝓑 : Set → Set
𝓑 = 𝓓 Nat Nat

instance
  𝓓-functor : {X Y : Set} → Functor (𝓓 X Y)
  Functor.map 𝓓-functor f (η x) = η (f x)
  Functor.map 𝓓-functor f (β⟨ i ⟩ 𝓭[_]) = β⟨ i ⟩ λ x → map f 𝓭[ x ]

  𝓓-monad : {X Y : Set} → Monad (𝓓 X Y)
  Monad.return_ 𝓓-monad = η_
  Monad.bind 𝓓-monad κ (η x) = κ x
  Monad.bind 𝓓-monad κ (β⟨ i ⟩ 𝓭[_]) = β⟨ i ⟩ λ x → Monad.bind 𝓓-monad κ 𝓭[ x ]

{-# DISPLAY 𝓓-functor f 𝓭 = map f 𝓭 #-}
{-# DISPLAY 𝓓-monad κ 𝓭 = 𝓭 ≫= κ #-}

-- A dialogue may be run against a choice sequence.
_$_
  : {X Y Z : Set}
  → 𝓓 X Y Z
  → (X → Y)
  → Z
(η x) $ α = x
β⟨ i ⟩ 𝓭[_] $ α =
  𝓭[ α i ] $ α

generic
  : {X Y : Set}
  → 𝓓 X Y X
  → 𝓓 X Y Y
generic 𝓭 =
  𝓭 ≫= λ i →
    β⟨ i ⟩ η_

module ⊢ where
  _$¹_
    : {X Y Z : Set}
    → (𝓭 : 𝓓 X Y Z)
    → {α β : X → Y}
    → (∀ i → α i ≡ β i)
    → 𝓭 $ α ≡ 𝓭 $ β

  (η x) $¹ h =
    refl

  _$¹_ (β⟨ i ⟩ 𝓭[_]) {α = α} {β = β} h rewrite h i =
    𝓭[ β i ] $¹ h


  $-natural
    : {X Y Z W : Set}
    → (f : Z → W)
    → (𝓭 : 𝓓 X Y Z)
    → (α : X → Y)
    → f (𝓭 $ α) ≡ map f 𝓭 $ α

  $-natural f (η x) α =
    refl

  $-natural f (β⟨ i ⟩ 𝓭[_]) α =
    $-natural f 𝓭[ α i ] α


  $-≫=
    : {X Y Z W : Set}
    → {𝓭[_] : Z → 𝓓 X Y W}
    → (𝓮 : 𝓓 X Y Z)
    → (α : X → Y)
    → 𝓭[ 𝓮 $ α ] $ α ≡ (𝓮 ≫= 𝓭[_]) $ α

  $-≫= (η x) α =
    refl

  $-≫= (β⟨ i ⟩ 𝓭[_]) α =
    $-≫= 𝓭[ α i ] α


  generic-diagram
    : {X Y : Set}
    → (α : X → Y)
    → (𝓭 : 𝓓 X Y X)
    → α (𝓭 $ α) ≡ generic 𝓭 $ α

  generic-diagram α (η x) =
    refl

  generic-diagram α (β⟨ i ⟩ 𝓭[_]) =
    generic-diagram α 𝓭[ α i ]

