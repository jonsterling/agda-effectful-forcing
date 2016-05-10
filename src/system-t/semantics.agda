module System-T.Semantics where

open import Prelude.Finite
open import Prelude.Functor
open import Prelude.Monoidal hiding (_⇒_; _,_)
open import Prelude.Monad
open import Prelude.Natural
open import Prelude.String
open import Prelude.Path

import Context as Ctx
open Ctx hiding (⋄; _,_)
open Π using (_∘_)

open import Baire
open import Dialogue
open import System-T.Syntax

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

  ⟦_⟧ : ∀ {n τ} {Γ : Ctx n} → 𝔏.T ▹ Γ ⊢ᵀ τ → 𝒢.⟦ Γ ⟧ → 𝒱.⟦ τ ⟧
  ⟦ zero ⟧ _ = ze
  ⟦ succ ⟧ _ = su_
  ⟦ rec[ σ ] ⟧ _ = rec
  ⟦ ν i ⟧ ρ = ρ i
  ⟦ ƛ t ⟧ ρ = λ x → ⟦ t ⟧ (ρ 𝒢., x)
  ⟦ m · n ⟧ ρ = ⟦ m ⟧ ρ (⟦ n ⟧ ρ)

  ⟦_⟧₀ : ∀ {τ} → 𝔏.T ▹ Ctx.⋄ ⊢ᵀ τ → 𝒱.⟦ τ ⟧
  ⟦ t ⟧₀ = ⟦ t ⟧ 𝒢.⋄

module TΩ where
  open LogicalRelations id public

  ⟦_⟧ : ∀ {𝔏 n τ} {Γ : Ctx n} → 𝔏 ▹ Γ ⊢ᵀ τ → Point → 𝒢.⟦ Γ ⟧ → 𝒱.⟦ τ ⟧
  ⟦ zero ⟧ α ρ = ze
  ⟦ succ ⟧ α ρ = su_
  ⟦ rec[ σ ] ⟧ α ρ = rec
  ⟦ ν i ⟧ α ρ = ρ i
  ⟦ ƛ t ⟧ α ρ = λ x → ⟦ t ⟧ α (ρ 𝒢., x)
  ⟦ m · n ⟧ α ρ = ⟦ m ⟧ α ρ (⟦ n ⟧ α ρ)
  ⟦ Ω ⟧ α ρ = α

  ⟦_⟧₀ : ∀ {𝔏 τ} → 𝔏 ▹ Ctx.⋄ ⊢ᵀ τ → Point → 𝒱.⟦ τ ⟧
  ⟦ t ⟧₀ α = ⟦ t ⟧ α 𝒢.⋄

module 𝔅 where
  open LogicalRelations 𝔅 public

  Ext[_] : {X : Set} (τ : Type) → (X → 𝒱.⟦ τ ⟧) → 𝔅 X → 𝒱.⟦ τ ⟧
  Ext[ ` _ ] f x = x ≫= f
  Ext[ σ ⇒ τ ] g δ s = Ext[ τ ] (λ x → g x s) δ

  ⟦_⟧ : ∀ {𝔏 n τ} {Γ : Ctx n} → 𝔏 ▹ Γ ⊢ᵀ τ → 𝒢.⟦ Γ ⟧ → 𝒱.⟦ τ ⟧
  ⟦ zero ⟧ ρ = η ze
  ⟦ succ ⟧ ρ = map su_
  ⟦ rec[ σ ] ⟧ ρ ih z = Ext[ σ ] (rec (ih ∘ η) z)
  ⟦ ν i ⟧ ρ = ρ i
  ⟦ ƛ t ⟧ ρ = λ x → ⟦ t ⟧ (ρ 𝒢., x)
  ⟦ m · n ⟧ ρ = ⟦ m ⟧ ρ (⟦ n ⟧ ρ)
  ⟦ Ω ⟧ ρ = Ext[ ` nat ] (ϝ η)

  ⟦_⟧₀ : ∀ {𝔏 τ} → 𝔏 ▹ Ctx.⋄ ⊢ᵀ τ → 𝒱.⟦ τ ⟧
  ⟦ t ⟧₀ = ⟦ t ⟧ 𝒢.⋄
