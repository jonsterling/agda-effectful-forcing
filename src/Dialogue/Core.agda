module Dialogue.Core where

open import Prelude.Natural
open import Prelude.Functor
open import Prelude.Monad
open import Prelude.Path

-- An Escardó dialogue, representing a functional on a space whose
-- neighborhoods are lists of Y.
data 𝓓 (Y Z : Set) : Set where
  -- η x means that the result is x.
  η_
    : Z
    → 𝓓 Y Z

  -- β⟨ i ⟩ 𝓭[_] means that we request the ith element x of the choice sequence
  -- and proceed with 𝓭[x].
  β⟨_⟩
    : Nat
    → (Y → 𝓓 Y Z)
    → 𝓓 Y Z

-- 𝓑 represents functionals on the Baire space.
𝓑 : Set → Set
𝓑 = 𝓓 Nat

instance
  𝓓-functor : {Y : Set} → Functor (𝓓 Y)
  Functor.map 𝓓-functor f (η x) = η (f x)
  Functor.map 𝓓-functor f (β⟨ i ⟩ 𝓭[_]) = β⟨ i ⟩ λ x → map f 𝓭[ x ]

  𝓓-monad : {Y : Set} → Monad (𝓓 Y)
  Monad.return_ 𝓓-monad = η_
  Monad.bind 𝓓-monad κ (η x) = κ x
  Monad.bind 𝓓-monad κ (β⟨ i ⟩ 𝓭[_]) = β⟨ i ⟩ λ x → Monad.bind 𝓓-monad κ 𝓭[ x ]

{-# DISPLAY 𝓓-functor f 𝓭 = map f 𝓭 #-}
{-# DISPLAY 𝓓-monad κ 𝓭 = 𝓭 ≫= κ #-}


Seq : Set → Set
Seq X = Nat → X

_^ω : Set → Set
X ^ω = Seq X

{-# DISPLAY Seq X = X ^ω #-}

-- A dialogue may be run against a choice sequence.
_$_
  : {Y Z : Set}
  → 𝓓 Y Z
  → Y ^ω
  → Z
(η x) $ α = x
β⟨ i ⟩ 𝓭[_] $ α =
  𝓭[ α i ] $ α

generic
  : 𝓑 Nat
  → 𝓑 Nat
generic 𝓭 =
  𝓭 ≫= λ i →
    β⟨ i ⟩ η_

module ⊢ where
  _$¹_
    : {Y Z : Set} (𝓭 : 𝓓 Y Z) {α β : Y ^ω}
    → (∀ i → α i ≡ β i)
    → 𝓭 $ α ≡ 𝓭 $ β

  (η x) $¹ h =
    refl

  _$¹_ (β⟨ i ⟩ 𝓭[_]) {α = α} {β = β} h rewrite h i =
    𝓭[ β i ] $¹ h


  $-natural
    : {Y Z W : Set}
    → (f : Z → W)
    → (𝓭 : 𝓓 Y Z)
    → (α : Y ^ω)
    → f (𝓭 $ α) ≡ map f 𝓭 $ α

  $-natural f (η x) α =
    refl

  $-natural f (β⟨ i ⟩ 𝓭[_]) α =
    $-natural f 𝓭[ α i ] α


  $-≫=
    : {X Y : Set}
    → {𝓭[_] : X → 𝓑 Y}
    → (𝓮 : 𝓑 X)
    → (α : Nat ^ω)
    → 𝓭[ 𝓮 $ α ] $ α ≡ (𝓮 ≫= 𝓭[_]) $ α

  $-≫= (η x) α =
    refl

  $-≫= (β⟨ i ⟩ 𝓭[_]) α =
    $-≫= 𝓭[ α i ] α


  generic-diagram
    : (α : Nat ^ω)
    → (𝓭 : 𝓑 Nat)
    → α (𝓭 $ α) ≡ generic 𝓭 $ α

  generic-diagram α (η x) =
    refl

  generic-diagram α (β⟨ i ⟩ 𝓭[_]) =
    generic-diagram α 𝓭[ α i ]

