module System-T.Semantics where

open import Prelude.Finite
open import Prelude.Functor hiding (map)
open import Prelude.Monad hiding (_≫=_)
open import Prelude.Monoidal hiding (_⇒_; _,_)
open import Prelude.Natural
open import Prelude.String
open import Prelude.Path

import Context as Ctx
open Ctx hiding (⋄; _,_)
open Π using (_∘_)

import Baire
import Dialogue as 𝓓

open import System-T.Syntax

open Functor 𝓓.𝓓-functor
open Monad 𝓓.𝓓-monad

private
  id : {ℓ : _} {A : Set ℓ} → A → A
  id x = x

-- We construct the logical relations relative to a functor in which
-- to interpret the base types.
module LogicalRelations (F : Set → Set) where
  module 𝒱 where
    ⟦_⟧₀ : BaseType → Set
    ⟦ nat ⟧₀ = Nat

    ⟦_⟧ : Type → Set
    ⟦ ` b ⟧ = F ⟦ b ⟧₀
    ⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

  module 𝒢 where
    ⟦_⟧ : {n : Nat} → Ctx n → Set
    ⟦ Γ ⟧ = (i : Fin _) → 𝒱.⟦ Γ [ i ] ⟧

    ⋄ : ⟦ Ctx.⋄ ⟧
    ⋄ ()

    _,_ : ∀ {n} {Γ : Ctx n} {σ : Type} → ⟦ Γ ⟧ → 𝒱.⟦ σ ⟧ → ⟦ Γ Ctx., σ ⟧
    (ρ , x) ze = x
    (ρ , x) (su i) = ρ i

rec : {X : Set} → (Nat → X → X) → X → Nat → X
rec f x ze = x
rec f x (su n) = f n (rec f x n)

module T where
  open LogicalRelations id public

  ⟦_⟧
    : ∀ {n τ} {Γ : Ctx n}
    → 𝓛.T ▹ Γ ⊢ᵀ τ
    → 𝒢.⟦ Γ ⟧
    → 𝒱.⟦ τ ⟧
  ⟦ zero ⟧ _ = ze
  ⟦ succ ⟧ _ = su_
  ⟦ rec[ σ ] ⟧ _ = rec
  ⟦ ν i p ⟧ ρ rewrite p = ρ i
  ⟦ ƛ t ⟧ ρ = λ x → ⟦ t ⟧ (ρ 𝒢., x)
  ⟦ m · n ⟧ ρ = ⟦ m ⟧ ρ (⟦ n ⟧ ρ)

  ⟦_⟧₀
    : ∀ {τ}
    → 𝓛.T ▹ Ctx.⋄ ⊢ᵀ τ
    → 𝒱.⟦ τ ⟧
  ⟦ t ⟧₀ = ⟦ t ⟧ 𝒢.⋄

module TΩ where
  open LogicalRelations id public
  open Baire

  ⟦_⟧
    : ∀ {𝓛 n τ} {Γ : Ctx n}
    → 𝓛 ▹ Γ ⊢ᵀ τ
    → Point
    → 𝒢.⟦ Γ ⟧
    → 𝒱.⟦ τ ⟧
  ⟦ zero ⟧ α ρ = ze
  ⟦ succ ⟧ α ρ = su_
  ⟦ rec[ σ ] ⟧ α ρ = rec
  ⟦ ν i p ⟧ α ρ rewrite p = ρ i
  ⟦ ƛ t ⟧ α ρ = λ x → ⟦ t ⟧ α (ρ 𝒢., x)
  ⟦ m · n ⟧ α ρ = ⟦ m ⟧ α ρ (⟦ n ⟧ α ρ)
  ⟦ Ω ⟧ α ρ = α

  ⟦_⟧₀
    : ∀ {𝓛 τ}
    → 𝓛 ▹ Ctx.⋄ ⊢ᵀ τ
    → Point
    → 𝒱.⟦ τ ⟧
  ⟦ t ⟧₀ α = ⟦ t ⟧ α 𝒢.⋄

module 𝓑 where
  open Baire
  open LogicalRelations 𝓓.𝓑 public

  Ext[_]
    : {X : Set} (τ : Type)
    → (X → 𝒱.⟦ τ ⟧)
    → 𝓓.𝓑 X
    → 𝒱.⟦ τ ⟧
  Ext[ ` 𝔟 ] f x = x ≫= f
  Ext[ σ ⇒ τ ] g 𝓭 s = Ext[ τ ] (λ x → g x s) 𝓭

  ⟦_⟧
    : ∀ {𝓛 n τ} {Γ : Ctx n}
    → 𝓛 ▹ Γ ⊢ᵀ τ
    → 𝒢.⟦ Γ ⟧
    → 𝒱.⟦ τ ⟧
  ⟦ zero ⟧ ρ = 𝓓.η ze
  ⟦ succ ⟧ ρ = map su_
  ⟦ rec[ σ ] ⟧ ρ ih z m = Ext[ σ ] (λ x → rec (ih ∘ 𝓓.η_) z x) m
  ⟦ ν x p ⟧ ρ rewrite p = ρ x
  ⟦ ƛ t ⟧ ρ = λ x → ⟦ t ⟧ (ρ 𝒢., x)
  ⟦ m · n ⟧ ρ = ⟦ m ⟧ ρ (⟦ n ⟧ ρ)
  ⟦ Ω ⟧ ρ 𝓭 = 𝓭 ≫= λ i → 𝓓.ϝ i 𝓓.η_

  ⟦_⟧₀
    : ∀ {𝓛 τ}
    → 𝓛 ▹ Ctx.⋄ ⊢ᵀ τ
    → 𝒱.⟦ τ ⟧
  ⟦ t ⟧₀ =
    ⟦ t ⟧ 𝒢.⋄


module Testing where
  open 𝓑

  add : 𝓛.TΩ ▹ Ctx.⋄ ⊢ᵀ ` nat ⇒ ` nat ⇒ ` nat
  add = rec[ ` nat ] · ƛ succ

  test : 𝓓.𝓑 Nat
  test = ⟦ add · (Ω · zero) · (Ω · zero) ⟧₀

open Baire

-- The following theorem must be proved via logical relations, following Escardó's
-- proof here: http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue-lambda.html#18185.
postulate
  interpretation-correct
    : (α : Point)
    → (F : 𝓛.TΩ ▹ Ctx.⋄ ⊢ᵀ ((` nat ⇒ ` nat) ⇒ ` nat))
    → 𝓓.⟦ 𝓑.⟦ F · Ω ⟧₀ ⟧ α ≡ TΩ.⟦ F · Ω ⟧₀ α
