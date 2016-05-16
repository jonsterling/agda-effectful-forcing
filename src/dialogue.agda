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
  ζ_ : 𝓓 Y Z → 𝓓 Y Z
  ϝ : (Y → 𝓓 Y Z) → 𝓓 Y Z

cons : {X : Set} → X → X ^ω → X ^ω
cons x α ze = x
cons x α (su i) = α i

eval : {Y Z : Set} → 𝓓 Y Z → List Y → Y ^ω → Z
eval (η x) U α = x
eval (ζ 𝓭) [] α = eval 𝓭 [] α
eval (ζ 𝓭) (x ∷ U) α = eval 𝓭 U (cons x α)
eval (ϝ 𝓭[_]) U α = eval 𝓭[ α 0 ] (α 0 ∷ U) (α ∘ su_)


⟦_⟧ : {Y Z : Set} → 𝓓 Y Z → Y ^ω → Z
⟦ 𝓭 ⟧ = eval 𝓭 []

-- {-# DISPLAY eval 𝓭 U α = ⟦ 𝓭 ⟧ α #-}

-- A mental construction of a functional on the Baire space
𝓑 : Set → Set
𝓑 = 𝓓 Nat

instance
  𝓓-functor : Functor 𝓑
  Functor.map 𝓓-functor f (η x) = η (f x)
  Functor.map 𝓓-functor f (ζ 𝓭) = ζ (map f 𝓭)
  Functor.map 𝓓-functor f (ϝ 𝓭[_]) = ϝ λ x → map f 𝓭[ x ]

  𝓓-monad : Monad 𝓑
  Monad.return_ 𝓓-monad = η_
  Monad.bind 𝓓-monad κ (η x) = κ x
  Monad.bind 𝓓-monad κ (ζ 𝓭) = ζ Monad.bind 𝓓-monad κ 𝓭
  Monad.bind 𝓓-monad κ (ϝ 𝓭[_]) = ϝ λ x → Monad.bind 𝓓-monad κ 𝓭[ x ]

{-# DISPLAY 𝓓-functor f 𝓭 = map f 𝓭 #-}
{-# DISPLAY 𝓓-monad κ 𝓭 = 𝓭 ≫= κ #-}

module ⊢ where

  eval-natural
    : {X Y : Set}
    → (f : X → Y)
    → (𝓭 : 𝓑 X)
    → (U : List Nat)
    → (α : Nat ^ω)
    → f (eval 𝓭 U α) ≡ eval (map f 𝓭 ) U α
  eval-natural f (η x) U α =
    refl
  eval-natural f (ζ 𝓭) [] α rewrite eval-natural f 𝓭 [] α = refl
  eval-natural f (ζ 𝓭) (x ∷ U) α rewrite eval-natural f 𝓭 U (cons x α) = refl
  eval-natural f (ϝ 𝓭[_]) U α =
    eval-natural f 𝓭[ α 0 ] (α 0 ∷ U) (α ∘ su_)

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
