module Baire where

open import Prelude.List
open import Prelude.Monoidal
open import Prelude.Natural
open import Prelude.Path

open import Prelude.Functor
open import Prelude.Monad

open import Dialogue

open Π using (_∘_)

-- The Baire Space is Brouwer's universal spread. We define its points and
-- neighborhoods below.

Seq : Set → Set
Seq X = Nat → X

-- A point in the Baire spread is a sequence of natural numbers.
Point : Set
Point = Seq Nat

-- A neighborhood in the Baire spread is a finite list of natural numbers.
Neigh : Set
Neigh = List Nat

-- The type of mental constructions (dialogues) of functionals on the Baire spread.
𝔅 : Set → Set
𝔅 = 𝔇 Nat Nat

instance
  𝔅-Functor : Functor 𝔅
  Functor.map 𝔅-Functor f (η x) = η (f x)
  Functor.map 𝔅-Functor f (ϝ φ i) = map f (φ i)

  𝔅-Monad : Monad 𝔅
  Monad.return_ 𝔅-Monad = η
  Monad.bind 𝔅-Monad κ (η x) = κ x
  Monad.bind 𝔅-Monad κ (ϝ φ i) = ϝ (λ j → Monad.bind 𝔅-Monad κ (φ j)) i

infixr 3 _⊩_≡_

data _⊩_≡_ {X : Set} : Neigh → Seq X → Seq X → Set where
  []
    : {α β : Seq X}
    → [] ⊩ α ≡ β

  _∷_
    : {α β : Seq X} {i : Nat} {U : Neigh}
    → α i ≡ β i
    → U ⊩ α ≡ β
    → i ∷ U ⊩ α ≡ β

-- The usual ∀∃ definition of continuity on the Baire spread.
continuous : (Point → Nat) → Set
continuous f =
  (α : Point) →
    Σ[ Neigh ∋ U ]
      ((β : Point) → U ⊩ α ≡ β → f α ≡ f β)

-- Every dialogue is continuous.
𝔇-continuity : (δ : 𝔅 Nat) → continuous 𝔇[ δ ]
𝔇-continuity (η n) α = [] ▸ λ β p → refl
𝔇-continuity (ϝ φ i) α = i ∷ U ▸ λ { β (p ∷ ps) → criss β ps ≡.⟓ cross β p }
  where
    IH : continuous 𝔇[ φ (α i) ]
    IH = 𝔇-continuity (φ (α i))

    U : Neigh
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
