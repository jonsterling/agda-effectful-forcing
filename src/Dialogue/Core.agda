{-# OPTIONS --without-K #-}

module Dialogue.Core where

open import Basis

-- An Escardó dialogue, representing a functional on a space whose
-- neighborhoods are lists of Y.
data 𝔈 (X Y Z : Set) : Set where
  -- η x means that the result is x.
  η_
    : Z
    → 𝔈 X Y Z

  -- β⟨ i ⟩ 𝓭 means that we request the ith element x of the choice sequence
  -- and proceed with 𝓭 x.
  ?⟨_⟩
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

  -- ϝ 𝓭 means that we request the *current* element x of the choice sequence
  -- and proceed with 𝓭 x.
  ϝ
    : (Y → 𝔅 Y Z)
    → 𝔅 Y Z


private
  variable {X Y} : Set

  𝔈-bind : {A B : Set} → (A → 𝔈 X Y B) → 𝔈 X Y A → 𝔈 X Y B
  𝔈-bind f (η x) = f x
  𝔈-bind f (?⟨ i ⟩ m) = ?⟨ i ⟩ λ x → 𝔈-bind f (m x)

  𝔈-bind/ρ : {A : Set} (m : 𝔈 X Y A) → 𝔈-bind η_ m ≡ m
  𝔈-bind/ρ (η x) = refl
  𝔈-bind/ρ (?⟨ i ⟩ m) =
    ≡.cong ?⟨ i ⟩
      (funext λ x →
       𝔈-bind/ρ (m x))

  𝔈-bind/α : {A B C : Set} (m : 𝔈 X Y A) (f : A → 𝔈 X Y B) (g : B → 𝔈 X Y C) → 𝔈-bind g (𝔈-bind f m) ≡ 𝔈-bind (λ x → 𝔈-bind g (f x)) m
  𝔈-bind/α (η x) f g = refl
  𝔈-bind/α (?⟨ i ⟩ m) f g =
    ≡.cong ?⟨ i ⟩
     (funext λ x →
      𝔈-bind/α (m x) f g)

instance
  𝔈-monad : {X Y : Set} → Monad (𝔈 X Y)
  Monad.ret 𝔈-monad = η_
  Monad.bind 𝔈-monad = 𝔈-bind
  Monad.law/λ 𝔈-monad _ _ = refl
  Monad.law/ρ 𝔈-monad = 𝔈-bind/ρ
  Monad.law/α 𝔈-monad = 𝔈-bind/α

-- An Escardó dialogue may be run against a choice sequence.
𝔈[_⋄_]
  : {X Y Z : Set}
  → 𝔈 X Y Z
  → (X → Y)
  → Z
𝔈[ (η x) ⋄ α ] = x
𝔈[ ?⟨ i ⟩ m ⋄ α ] =
  𝔈[ m (α i) ⋄ α ]


-- A Brouwerian dialogue may be run against a choice sequence.
𝔅[_⋄_] : {Y Z : Set} → 𝔅 Y Z → (Nat → Y) → Z
𝔅[ η x ⋄ α ] = x
𝔅[ ϝ m ⋄ α ] = 𝔅[ m (α 0) ⋄ (α ∘ suc) ]


generic
  : {X Y : Set}
  → 𝔈 X Y X
  → 𝔈 X Y Y
generic m = do
  i ← m
  ?⟨ i ⟩ ret

module ⊢ where
  ⋄-extensional
    : {X Y Z : Set}
    → (m : 𝔈 X Y Z)
    → {α β : X → Y}
    → (∀ i → α i ≡ β i)
    → 𝔈[ m ⋄ α ] ≡ 𝔈[ m ⋄ β ]

  ⋄-extensional (η _) _ =
    refl

  ⋄-extensional (?⟨ i ⟩ m) {α} {β} h =
    ≡.seq
     (⋄-extensional (m (α i)) h)
     (≡.cong
      (λ ■ → 𝔈[ m ■ ⋄ β ])
      (h i))


  ⋄-natural
    : {X Y Z W : Set}
    → (f : Z → W)
    → (m : 𝔈 X Y Z)
    → (α : X → Y)
    → f 𝔈[ m ⋄ α ] ≡ 𝔈[ map f m ⋄ α ]

  ⋄-natural f (η x) α =
    refl

  ⋄-natural f (?⟨ _ ⟩ m) α =
    ⋄-natural f (m _) α


  ⋄-commutes-with-bind
    : {X Y Z W : Set}
    → {m : Z → 𝔈 X Y W}
    → (n : 𝔈 X Y Z)
    → (α : X → Y)
    → 𝔈[ m 𝔈[ n ⋄ α ] ⋄ α ] ≡ 𝔈[ (n >>= m) ⋄ α ]

  ⋄-commutes-with-bind (η _) _ =
    refl

  ⋄-commutes-with-bind (?⟨ _ ⟩ m) α =
    ⋄-commutes-with-bind (m _) α


  generic-diagram
    : {X Y : Set}
    → (α : X → Y)
    → (m : 𝔈 X Y X)
    → α 𝔈[ m ⋄ α ] ≡ 𝔈[ generic m ⋄ α ]

  generic-diagram α (η x) =
    refl

  generic-diagram α (?⟨ _ ⟩ m) =
    generic-diagram α (m _)
