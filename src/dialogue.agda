module Dialogue where

open import Prelude.Functor
open import Prelude.Monad
open import Prelude.Monoidal
open import Prelude.Natural
open import Prelude.Path
open import Prelude.List

open Π using (_∘_)

Seq : Set → Set
Seq X = Nat → X

_^ω : Set → Set
X ^ω = Seq X

{-# DISPLAY Seq X = X ^ω #-}

-- A dialogue tree is precisely Brouwer's notion of a "mental construction"
-- of a functional on the points of a spread.
data 𝓓 (Y Z : Set) : Set where
  η_ : Z → 𝓓 Y Z
  ϝ : Nat → (Y → 𝓓 Y Z) → 𝓓 Y Z

data 𝓓ₙ (Y Z : Set) : Set where
  η_ : Z → 𝓓ₙ Y Z
  ϝ : (Y → 𝓓ₙ Y Z) → 𝓓ₙ Y Z

nth : {Y : Set} → List Y → Nat → Y ⊕ 𝟙
nth [] i = ⊕.inr 𝟙.*
nth (x ∷ xs) ze = ⊕.inl x
nth (x ∷ xs) (su_ i) = nth xs i


-- TODO: This needs to be reimplemented structurally and proved correct.
{-# TERMINATING #-}
normalize : {Y Z : Set} → List Y → 𝓓 Y Z → 𝓓ₙ Y Z
normalize U (η x) = η x
normalize U (ϝ i 𝓭[_]) with nth U i
normalize U (ϝ i 𝓭[_]) | ⊕.inl x = normalize U 𝓭[ x ]
normalize U (ϝ i 𝓭[_]) | ⊕.inr _ = ϝ λ x → normalize (U ⌢ x) (ϝ i 𝓭[_])
  where
    _⌢_ : {Y : Set} → List Y → Y → List Y
    [] ⌢ x = x ∷ []
    (x ∷ xs) ⌢ y = x ∷ (xs ⌢ y)


normalize₀ : {Y Z : Set} → 𝓓 Y Z → 𝓓ₙ Y Z
normalize₀ = normalize []

eval : {Y Z : Set} → 𝓓 Y Z → Y ^ω → Z
eval (η x) α = x
eval (ϝ i 𝓭[_]) α = eval 𝓭[ α i ] α

evalₙ : {Y Z : Set} → 𝓓ₙ Y Z → Y ^ω → Z
evalₙ (η x) α = x
evalₙ (ϝ 𝓭[_]) α = evalₙ 𝓭[ α 0 ] (α ∘ su_)

⟦_⟧ : {Y Z : Set} → 𝓓 Y Z → Y ^ω → Z
⟦ 𝓭 ⟧ = eval 𝓭

⟦_⟧ₙ : {Y Z : Set} → 𝓓ₙ Y Z → Y ^ω → Z
⟦ 𝓭 ⟧ₙ = evalₙ 𝓭

{-# DISPLAY eval 𝓭 U α = ⟦ 𝓭 ⟧ α #-}
{-# DISPLAY evalₙ 𝓭 U α = ⟦ 𝓭 ⟧ₙ α #-}

module Tests where

  id : Nat ^ω
  id x = x

  test : 𝓓 Nat Nat
  test = ϝ 4 λ x → ϝ 5 λ y → η (x Nat.+ y)

  test2 : 𝓓ₙ Nat Nat
  test2 = normalize₀ test


  test-eq : ⟦ test ⟧ id ≡ ⟦ normalize₀ test ⟧ₙ id
  test-eq = refl

postulate
  coherence : {Y Z : Set} (𝓭 : 𝓓 Y Z) (α : Y ^ω) → ⟦ 𝓭 ⟧ α ≡ ⟦ normalize₀ 𝓭 ⟧ₙ α

-- A mental construction of a functional on the Baire space
𝓑 : Set → Set
𝓑 = 𝓓 Nat

𝓑ₙ : Set → Set
𝓑ₙ = 𝓓ₙ Nat

instance
  𝓓-functor : Functor 𝓑
  Functor.map 𝓓-functor f (η x) = η (f x)
  Functor.map 𝓓-functor f (ϝ i 𝓭[_]) = ϝ i λ x → map f 𝓭[ x ]

  𝓓-monad : Monad 𝓑
  Monad.return_ 𝓓-monad = η_
  Monad.bind 𝓓-monad κ (η x) = κ x
  Monad.bind 𝓓-monad κ (ϝ i 𝓭[_]) = ϝ i λ x → Monad.bind 𝓓-monad κ 𝓭[ x ]

{-# DISPLAY 𝓓-functor f 𝓭 = map f 𝓭 #-}
{-# DISPLAY 𝓓-monad κ 𝓭 = 𝓭 ≫= κ #-}

module ⊢ where

  eval-natural
    : {X Y : Set}
    → (f : X → Y)
    → (𝓭 : 𝓑 X)
    → (α : Nat ^ω)
    → f (⟦ 𝓭 ⟧ α) ≡ ⟦ map f 𝓭 ⟧ α
  eval-natural f (η x) α =
    refl
  eval-natural f (ϝ i 𝓭[_]) α =
    eval-natural f 𝓭[ α i ] α

{-
  -- uh-oh! Is this even true?
  eval-bind-law
    : {X Y : Set}
    → (𝓯[_] : X → 𝓑 Y)
    → (𝓭 : 𝓑 X)
    → (α : Nat ^ω)
    → ⟦ 𝓯[ ⟦ 𝓭 ⟧ α ] ⟧ α ≡ ⟦ 𝓭 ≫= 𝓯[_] ⟧ α
  eval-bind-law 𝓯[_] (η x) α = refl
  eval-bind-law 𝓯[_] (ϝ 𝓭[_]) α = {!!}
-}
