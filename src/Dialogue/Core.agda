module Dialogue.Core where

open import Basis

-- An Escardó dialogue, representing a functional on a space whose
-- neighborhoods are lists of Y.
data 𝔈 (X Y Z : Set) : Set where
  -- η x means that the result is x.
  η_
    : Z
    → 𝔈 X Y Z

  -- β⟨ i ⟩ 𝓭[_] means that we request the ith element x of the choice sequence
  -- and proceed with 𝓭[x].
  β⟨_⟩
    : X
    → (Y → 𝔈 X Y Z)
    → 𝔈 X Y Z


-- In the normalized (Brouwerian) version of the dialogue tree, queries are
-- given in order.
data 𝔅 (Y Z : Set) : Set where
  -- η x means that the result is x.
  η_
    : Z
    → 𝔅 Y Z

  -- ϝ 𝓭[_] means that we request the *current* element x of the choice sequence
  -- and proceed with 𝓭[x].
  ϝ
    : (Y → 𝔅 Y Z)
    → 𝔅 Y Z


instance
  𝔈-functor : {X Y : Set} → Functor (𝔈 X Y)
  Functor.map 𝔈-functor f (η x) = η (f x)
  Functor.map 𝔈-functor f (β⟨ i ⟩ 𝓭[_]) = β⟨ i ⟩ λ x → map f 𝓭[ x ]

  𝔈-monad : {X Y : Set} → Monad (𝔈 X Y)
  Monad.return_ 𝔈-monad = η_
  Monad.bind 𝔈-monad κ (η x) = κ x
  Monad.bind 𝔈-monad κ (β⟨ i ⟩ 𝓭[_]) = β⟨ i ⟩ λ x → Monad.bind 𝔈-monad κ 𝓭[ x ]


-- An Escardó dialogue may be run against a choice sequence.
𝔈[_⋄_]
  : {X Y Z : Set}
  → 𝔈 X Y Z
  → (X → Y)
  → Z
𝔈[ (η x) ⋄ α ] = x
𝔈[ β⟨ i ⟩ 𝓭[_] ⋄ α ] =
  𝔈[ 𝓭[ α i ] ⋄ α ]


-- A Brouwerian dialogue may be run against a choice sequence.
𝔅[_⋄_] : {Y Z : Set} → 𝔅 Y Z → (Nat → Y) → Z
𝔅[ η x ⋄ α ] = x
𝔅[ ϝ 𝓭[_] ⋄ α ] = 𝔅[ 𝓭[ α 0 ] ⋄ (α ∘ suc) ]


generic
  : {X Y : Set}
  → 𝔈 X Y X
  → 𝔈 X Y Y
generic 𝓭 =
  𝓭 ≫= λ i →
    β⟨ i ⟩ η_


module ⊢ where
  ⋄-extensional
    : {X Y Z : Set}
    → (𝓭 : 𝔈 X Y Z)
    → {α β : X → Y}
    → (∀ i → α i ≡ β i)
    → 𝔈[ 𝓭 ⋄ α ] ≡ 𝔈[ 𝓭 ⋄ β ]

  ⋄-extensional (η _) _ =
    refl

  ⋄-extensional (β⟨ i ⟩ 𝓭[_]) {α = α} {β = β} h rewrite h i =
    ⋄-extensional 𝓭[ β i ] h


  ⋄-natural
    : {X Y Z W : Set}
    → (f : Z → W)
    → (𝓭 : 𝔈 X Y Z)
    → (α : X → Y)
    → f 𝔈[ 𝓭 ⋄ α ] ≡ 𝔈[ map f 𝓭 ⋄ α ]

  ⋄-natural f (η x) α =
    refl

  ⋄-natural f (β⟨ i ⟩ 𝓭[_]) α =
    ⋄-natural f 𝓭[ α i ] α


  ⋄-commutes-with-≫=
    : {X Y Z W : Set}
    → {𝓭[_] : Z → 𝔈 X Y W}
    → (𝓮 : 𝔈 X Y Z)
    → (α : X → Y)
    → 𝔈[ 𝓭[ 𝔈[ 𝓮 ⋄ α ] ] ⋄ α ] ≡ 𝔈[ (𝓮 ≫= 𝓭[_]) ⋄ α ]

  ⋄-commutes-with-≫= (η x) α =
    refl

  ⋄-commutes-with-≫= (β⟨ i ⟩ 𝓭[_]) α =
    ⋄-commutes-with-≫= 𝓭[ α i ] α


  generic-diagram
    : {X Y : Set}
    → (α : X → Y)
    → (𝓭 : 𝔈 X Y X)
    → α 𝔈[ 𝓭 ⋄ α ] ≡ 𝔈[ generic 𝓭 ⋄ α ]

  generic-diagram α (η x) =
    refl

  generic-diagram α (β⟨ i ⟩ 𝓭[_]) =
    generic-diagram α 𝓭[ α i ]
