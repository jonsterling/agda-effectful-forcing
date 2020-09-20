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


instance
  𝔈-monad : {X Y : Set} → Monad (𝔈 X Y)
  Monad.ret 𝔈-monad = η_
  Monad.bind 𝔈-monad κ (η x) = κ x
  Monad.bind 𝔈-monad κ (?⟨ i ⟩ m) =
    ?⟨ i ⟩ λ x → bind κ (m x)

  Monad.law/λ 𝔈-monad a k = refl

  Monad.law/ρ 𝔈-monad (η x) = refl
  Monad.law/ρ 𝔈-monad (?⟨ i ⟩ m) =
    ≡.cong ?⟨ i ⟩
     (funext λ x →
      law/ρ (m x))

  Monad.law/α 𝔈-monad (η x) f g = refl
  Monad.law/α 𝔈-monad (?⟨ i ⟩ m) f g =
    ≡.cong ?⟨ i ⟩
     (funext λ x →
      law/α (m x) f g)



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

  ⋄-extensional (?⟨ i ⟩ m) h rewrite h i =
    ⋄-extensional (m _) h


  ⋄-natural
    : {X Y Z W : Set}
    → (f : Z → W)
    → (m : 𝔈 X Y Z)
    → (α : X → Y)
    → f 𝔈[ m ⋄ α ] ≡ 𝔈[ map f m ⋄ α ]

  ⋄-natural _ (η x) _ =
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
