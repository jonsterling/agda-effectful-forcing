module Baire where

open import Prelude.List
open import Prelude.Monoidal
open import Prelude.Natural
open import Prelude.Path

open import Prelude.Functor
open import Prelude.Monad

open import Dialogue

Seq : Set → Set
Seq X = Nat → X

Point : Set
Point = Seq Nat

Neigh : Set
Neigh = List Nat

𝔅 : Set → Set
𝔅 = 𝔇 Nat Nat

instance
  𝔅-Functor : Functor 𝔅
  Functor.map 𝔅-Functor f (η x) = η (f x)
  Functor.map 𝔅-Functor f (ϝ φ i) = Functor.map 𝔅-Functor f (φ i)

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

continuous : (Point → Nat) → Set
continuous f =
  (α : Point) →
    Σ[ Neigh ∋ U ]
      ((β : Point) → U ⊩ α ≡ β → f α ≡ f β)

𝔇-continuity : (δ : 𝔅 Nat) → continuous 𝔇[ δ ]
𝔇-continuity (η n) α = [] ▸ λ β p → refl
𝔇-continuity (ϝ φ i) α = i ∷ U ▸ λ { β (p ∷ ps) → criss β ps ≡.⟓ cross β p }
  where
    IH : (i : Nat) → continuous 𝔇[ φ (α i) ]
    IH i = 𝔇-continuity (φ (α i))

    U : Neigh
    U = Σ.fst (IH i α)

    criss : (β : Point) → U ⊩ α ≡ β → 𝔇[ φ (α i) ] α ≡ 𝔇[ φ (α i) ] β
    criss = Σ.snd (IH i α)

    cross : (β : Point) → α i ≡ β i → 𝔇[ φ (α i) ] β ≡ 𝔇[ φ (β i) ] β
    cross β = ≡.ap¹ (λ n → 𝔇[ φ n ] β)

continuity-extensional : (f g : Point → Nat) → ((α : Point) → f α ≡ g α) → continuous f → continuous g
continuity-extensional f g p c α with c α
continuity-extensional f g p c α | U ▸ φ = U ▸ λ β q → (p α) ≡.⁻¹ ≡.⟓ φ β q  ≡.⟓ p β

eloquent⇒continuous : (f : Point → Nat) → eloquent f → continuous f
eloquent⇒continuous f (δ ▸ δ≡) = continuity-extensional 𝔇[ δ ] f δ≡ (𝔇-continuity δ)
