module Baire where

open import Prelude.List
open import Prelude.Monoidal
open import Prelude.Natural
open import Prelude.Path

open import Prelude.Functor
open import Prelude.Monad

open import Dialogue
open import Snoc

open Π using (_∘_)

-- The Baire Space is Brouwer's universal spread.

Seq : Set → Set
Seq X = Nat → X

-- A point in the Baire spread is a sequence of natural numbers.
Point : Set
Point = Seq Nat

-- The type of mental constructions (dialogues) of functionals on the Baire spread.
𝔅 : Set → Set
𝔅 = 𝔇 Nat Nat

𝔅ₙ : Set → Set
𝔅ₙ = 𝔇ₙ Nat

instance
  𝔅ₙ-Functor : Functor 𝔅ₙ
  Functor.map 𝔅ₙ-Functor f (η x) = η (f x)
  Functor.map 𝔅ₙ-Functor f (ϝ φ) = ϝ λ x → map f (φ x)

  𝔅ₙ-Monad : Monad 𝔅ₙ
  Monad.return_ 𝔅ₙ-Monad = η
  Monad.bind 𝔅ₙ-Monad κ (η x) = κ x
  Monad.bind 𝔅ₙ-Monad κ (ϝ φ) = ϝ λ x → Monad.bind 𝔅ₙ-Monad κ (φ x)

instance
  𝔅-Functor : Functor 𝔅
  Functor.map 𝔅-Functor f (η x) = η (f x)
  Functor.map 𝔅-Functor f (ϝ φ i) = map f (φ i)

  𝔅-Monad : Monad 𝔅
  Monad.return_ 𝔅-Monad = η
  Monad.bind 𝔅-Monad κ (η x) = κ x
  Monad.bind 𝔅-Monad κ (ϝ φ i) = ϝ (λ j → Monad.bind 𝔅-Monad κ (φ j)) i

infixr 3 _⊩_≡_

data _⊩_≡_ {X : Set} : List Nat → Seq X → Seq X → Set where
  []
    : {α β : Seq X}
    → [] ⊩ α ≡ β

  _∷_
    : {α β : Seq X} {i : Nat} {U : List Nat}
    → α i ≡ β i
    → U ⊩ α ≡ β
    → i ∷ U ⊩ α ≡ β

-- The usual ∀∃ definition of continuity on the Baire spread.
continuous : (Point → Nat) → Set
continuous f =
  (α : Point) →
    Σ[ List Nat ∋ U ]
      ((β : Point) → U ⊩ α ≡ β → f α ≡ f β)

-- Every dialogue is continuous.
𝔇-continuity : (δ : 𝔅 Nat) → continuous 𝔇[ δ ]
𝔇-continuity (η n) α = [] ▸ λ β p → refl
𝔇-continuity (ϝ φ i) α = i ∷ U ▸ λ { β (p ∷ ps) → criss β ps ≡.⟓ cross β p }
  where
    IH : continuous 𝔇[ φ (α i) ]
    IH = 𝔇-continuity (φ (α i))

    U : List Nat
    U = Σ.fst (IH α)

    criss : (β : Point) → U ⊩ α ≡ β → 𝔇[ φ (α i) ] α ≡ 𝔇[ φ (α i) ] β
    criss = Σ.snd (IH α)

    cross : (β : Point) → α i ≡ β i → 𝔇[ φ (α i) ] β ≡ 𝔇[ φ (β i) ] β
    cross β = ≡.ap¹ (λ n → 𝔇[ φ n ] β)

-- Continuity respects extensional equivalence of functionals.
continuity-extensional
  : {f g : Point → Nat}
  → ((α : Point) → f α ≡ g α)
  → continuous f
  → continuous g
continuity-extensional f≡g f-cont α with f-cont α
... | U ▸ φ =
  U ▸ λ β α≡[U]β →
    f≡g α ⁻¹
      ⟓ φ β α≡[U]β
      ⟓ f≡g β
  where
    open ≡

-- Every «eloquent» functional is continuous, because it can be coded as a dialogue.
eloquent⇒continuous
  : {f : Point → Nat}
  → eloquent f
  → continuous f
eloquent⇒continuous (δ ▸ δ≡) =
  continuity-extensional δ≡ (𝔇-continuity δ)


head : Point → Nat
head α = α 0

tail : Point → Point
tail α i = α (su i)

take : Nat → Point → List Nat
take ze α = []
take (su n) α = head α ∷ take n (tail α)

TAKE : Nat
TAKE = 0

{-# DISPLAY take x y = TAKE x y #-}

pt : List Nat → Point
pt [] i = 0
pt (x ∷ U) ze = x
pt (x ∷ U) (su_ i) = pt U i

take-pt-id : ∀ U → take (List.len U) (pt U) ≡ U
take-pt-id [] = refl
take-pt-id (x ∷ U) rewrite take-pt-id U = refl

take-pt-snoc-id : ∀ U y → take (List.len U) (pt (U ⌢ y)) ≡ U
take-pt-snoc-id [] _ = refl
take-pt-snoc-id (x ∷ U) y rewrite take-pt-snoc-id U y = refl

snoc-cons-id : ∀ (U : List Nat) x y → x ∷ (U ⌢ y) ≡ (x ∷ U) ⌢ y
snoc-cons-id [] x y = refl
snoc-cons-id (x ∷ U) y z rewrite snoc-cons-id U x z = refl

cons : Nat → Point → Point
cons x α ze = x
cons x α (su_ i) = α i

prepend : List Nat → Point → Point
prepend [] α = α
prepend (x ∷ xs) α = cons x (prepend xs α)

_⊕<_ : List Nat → Point → Point
U ⊕< α = prepend U α

{-# DISPLAY prepend U α = U ⊕< α #-}
{-# DISPLAY cons x α  = x ∷ α #-}

take-len-prepend : ∀ U α → take (List.len U) (U ⊕< α) ≡ U
take-len-prepend [] α = refl
take-len-prepend (x ∷ U) α rewrite take-len-prepend U α = refl

postulate
  take-prepend-lemma : ∀ U n α β → n Nat.< List.len U → take n (U ⊕< α) ≡ take n (U ⊕< β)

take-len-cons-prepend : ∀ U α x → take (su (List.len U)) (cons x (U ⊕< α)) ≡ x ∷ U
take-len-cons-prepend [] α x = refl
take-len-cons-prepend (x ∷ U) α y rewrite take-len-cons-prepend U α y | take-len-prepend U α = refl

cons-snoc-prepend-law : ∀ U {α x n} → take n (U ⊕< (cons x α)) ≡ take n ((U ⌢ x) ⊕< α)
cons-snoc-prepend-law [] = refl
cons-snoc-prepend-law (x ∷ U) {n = ze} = refl
cons-snoc-prepend-law (x ∷ U) {α = α} {x = y} {n = su_ n} rewrite cons-snoc-prepend-law U {α = α} {x = y} {n = n} = refl
