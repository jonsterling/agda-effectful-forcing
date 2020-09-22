{-# OPTIONS --without-K #-}

module Dialogue.Core where

open import Basis

-- An Escardó dialogue, representing a functional on a space whose
-- neighborhoods are lists of Y.
data 𝔈 (X Y Z : Set) : Set where
  -- return x means that the result is x.
  return
    : Z
    → 𝔈 X Y Z

  -- ask i m means that we request the ith element x of the choice sequence
  -- and proceed with 𝓭 x.
  ask
    : X
    → (Y → 𝔈 X Y Z)
    → 𝔈 X Y Z


-- In the normalized (Brouwerian) version of the dialogue tree, queries are
-- given in order.
data 𝔅 (Y Z : Set) : Set where
  -- η x means that the result is x.
  spit
    : Z
    → 𝔅 Y Z

  -- ϝ 𝓭 means that we request the *current* element x of the choice sequence
  -- and proceed with 𝓭 x.
  bite
    : (Y → 𝔅 Y Z)
    → 𝔅 Y Z


private
  variable {X Y} : Set

  𝔈-bind : {A B : Set} → (A → 𝔈 X Y B) → 𝔈 X Y A → 𝔈 X Y B
  𝔈-bind f (return x) = f x
  𝔈-bind f (ask i m) = ask i λ x → 𝔈-bind f (m x)

  𝔈-bind/ρ : {A : Set} (m : 𝔈 X Y A) → 𝔈-bind return m ≡ m
  𝔈-bind/ρ (return x) = refl
  𝔈-bind/ρ (ask i m) =
    ≡.cong
     (ask i)
     (funext λ x →
      𝔈-bind/ρ (m x))

  𝔈-bind/α : {A B C : Set} {f : A → 𝔈 X Y B} {g : B → 𝔈 X Y C} (m : 𝔈 X Y A) → 𝔈-bind g (𝔈-bind f m) ≡ 𝔈-bind (𝔈-bind g ∘ f) m
  𝔈-bind/α (return x) = refl
  𝔈-bind/α (ask i m) =
    ≡.cong
     (ask i)
     (funext λ x →
      𝔈-bind/α (m x))

instance
  𝔈-monad : Monad (𝔈 X Y)
  Monad.ret 𝔈-monad = return
  Monad.bind 𝔈-monad = 𝔈-bind
  Monad.law/λ 𝔈-monad = refl
  Monad.law/ρ 𝔈-monad = 𝔈-bind/ρ
  Monad.law/α 𝔈-monad = 𝔈-bind/α


private
  variable Z W : Set

-- An Escardó dialogue may be run against a choice sequence.
𝔈[_⋄_] : 𝔈 X Y Z → (X → Y) → Z
𝔈[ return x ⋄ α ] = x
𝔈[ ask i m ⋄ α ] =
  𝔈[ m (α i) ⋄ α ]


-- A Brouwerian dialogue may be run against a choice sequence.
𝔅[_⋄_] : 𝔅 Y Z → (ℕ → Y) → Z
𝔅[ spit x ⋄ α ] = x
𝔅[ bite m ⋄ α ] = 𝔅[ m (α 0) ⋄ (α ∘ suc) ]


generic : 𝔈 X Y X → 𝔈 X Y Y
generic m = do
  i ← m
  ask i ret

module ⊢ where
  ⋄-extensional
    : (m : 𝔈 X Y Z)
    → {α β : X → Y}
    → (∀ i → α i ≡ β i)
    → 𝔈[ m ⋄ α ] ≡ 𝔈[ m ⋄ β ]

  ⋄-extensional (return _) _ =
    refl

  ⋄-extensional (ask i m) {α} {β} h =
    ≡.seq
     (⋄-extensional (m (α i)) h)
     (≡.cong
      (λ ■ → 𝔈[ m ■ ⋄ β ])
      (h i))

  ⋄-natural
    : (f : Z → W)
    → (m : 𝔈 X Y Z)
    → (α : X → Y)
    → f 𝔈[ m ⋄ α ] ≡ 𝔈[ map f m ⋄ α ]

  ⋄-natural f (return x) α =
    refl

  ⋄-natural f (ask _ m) α =
    ⋄-natural f (m _) α


  ⋄-commutes-with-bind
    : {m : Z → 𝔈 X Y W}
    → (n : 𝔈 X Y Z)
    → (α : X → Y)
    → 𝔈[ m 𝔈[ n ⋄ α ] ⋄ α ] ≡ 𝔈[ (n >>= m) ⋄ α ]

  ⋄-commutes-with-bind (return _) _ =
    refl

  ⋄-commutes-with-bind (ask _ m) α =
    ⋄-commutes-with-bind (m _) α


  generic-diagram
    : (α : X → Y)
    → (m : 𝔈 X Y X)
    → α 𝔈[ m ⋄ α ] ≡ 𝔈[ generic m ⋄ α ]

  generic-diagram α (return x) =
    refl

  generic-diagram α (ask _ m) =
    generic-diagram α (m _)
