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

cons : {X : Set} → X → X ^ω → X ^ω
cons x α ze = x
cons x α (su i) = α i

eval : {Y Z : Set} → 𝓓 Y Z → Y ^ω → Z
eval (η x) α = x
eval (ϝ i 𝓭[_]) α = eval 𝓭[ α i ] α


⟦_⟧ : {Y Z : Set} → 𝓓 Y Z → Y ^ω → Z
⟦ 𝓭 ⟧ = eval 𝓭

{-# DISPLAY eval 𝓭 U α = ⟦ 𝓭 ⟧ α #-}

-- A mental construction of a functional on the Baire space
𝓑 : Set → Set
𝓑 = 𝓓 Nat

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
