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
  Ext[ σ ⇒ τ ] g δ s = Ext[ τ ] (λ x → g x s) δ

  ⟦_⟧
    : ∀ {𝓛 n τ} {Γ : Ctx n}
    → 𝓛 ▹ Γ ⊢ᵀ τ
    → 𝒢.⟦ Γ ⟧
    → 𝒱.⟦ τ ⟧
  ⟦ zero ⟧ ρ = 𝓓.η ze
  ⟦ succ ⟧ ρ = map su_
  ⟦ rec[ σ ] ⟧ ρ ih z = Ext[ σ ] (rec (ih ∘ 𝓓.η_) z)
  ⟦ ν i p ⟧ ρ rewrite p = ρ i
  ⟦ ƛ t ⟧ ρ = λ x → ⟦ t ⟧ (ρ 𝒢., x)
  ⟦ m · n ⟧ ρ = ⟦ m ⟧ ρ (⟦ n ⟧ ρ)
  ⟦ Ω ⟧ ρ = Ext[ ` nat ] go
    where
      go : Nat → 𝓓.𝓑 Nat
      go ze = 𝓓.ϝ 𝓓.η_
      go (su i) = 𝓓.ϝ λ α₀ → go i

  ⟦_⟧₀
    : ∀ {𝓛 τ}
    → 𝓛 ▹ Ctx.⋄ ⊢ᵀ τ
    → 𝒱.⟦ τ ⟧
  ⟦ t ⟧₀ = ⟦ t ⟧ 𝒢.⋄


open Baire

-- The following theorem must be proved via logical relations, following Escardó's
-- proof here: http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue-lambda.html#18185.
postulate
  coherence
    : (α : Point)
    → (F : 𝓛.TΩ ▹ Ctx.⋄ ⊢ᵀ ((` nat ⇒ ` nat) ⇒ ` nat))
    → 𝓓.⟦ 𝓑.⟦ F · Ω ⟧₀ ⟧ α ≡ TΩ.⟦ F · Ω ⟧₀ α


module Coherence where

  -- Our logical relation. I have a feeling we may need to adjust either it,
  -- or the interpretation.
  𝓡[_]
    : (σ : Type)
    → (Point → T.𝒱.⟦ σ ⟧)
    → 𝓑.𝒱.⟦ σ ⟧
    → Set
  𝓡[ ` 𝔟 ] F 𝓭 =
    (α : Point)
      → F α ≡ 𝓓.⟦ 𝓭 ⟧ α
  𝓡[ σ ⇒ τ ] f g =
    (F : Point → T.𝒱.⟦ σ ⟧)
    (𝓭 : 𝓑.𝒱.⟦ σ ⟧)
      → 𝓡[ σ ] F 𝓭
      → 𝓡[ τ ] (λ α → f α (F α)) (g 𝓭)

  𝓡⋆[_]
    : {n : Nat}
    → (Γ : Ctx n)
    → (Point → TΩ.𝒢.⟦ Γ ⟧)
    → 𝓑.𝒢.⟦ Γ ⟧
    → Set
  𝓡⋆[ Γ ] ρ₀ ρ₁ =
    (i : Fin _)
      → 𝓡[ Γ Ctx.[ i ] ] (λ α → ρ₀ α i) (ρ₁ i)

  𝓡-Ext-lemma
    : (σ : Type) (F[_] : Nat → Point → T.𝒱.⟦ σ ⟧) (𝓭[_] : Nat → 𝓑.𝒱.⟦ σ ⟧)
    → (∀ k → 𝓡[ σ ] F[ k ] 𝓭[ k ])
    → (F : Point → Nat)
    → (𝓭 : 𝓓.𝓑 Nat)
    → 𝓡[ ` nat ] F 𝓭
    → 𝓡[ σ ] (λ α → F[ F α ] α) (𝓑.Ext[ σ ] 𝓭[_] 𝓭)
  𝓡-Ext-lemma (` 𝔟) F[_] 𝓭[_] p F 𝓭 q = λ α → fact α
    where
      fact : ∀ α → F[ F α ] α ≡ 𝓓.⟦ 𝓭 ≫= 𝓭[_] ⟧ α
      fact α = ≡.ap¹ (λ x → F[ x ] α) (q α) ≡.⟓ {!!}


--    where
--      fact₀ : ∀ α → 𝓓.⟦ 𝓭[ 𝓓.⟦ 𝓭 ⟧ α ] ⟧ α ≡ 𝓓.⟦ (𝓑.Ext[ (` 𝔟) ] 𝓭[_] 𝓭) ⟧ α
--      fact₀ = {!!}

  𝓡-Ext-lemma (σ ⇒ σ₁) F[_] 𝓭[_] p F 𝓭 q = {!!}

  main-lemma
    : {n : Nat} {Γ : Ctx n} {σ : Type}
    → (M : 𝓛.TΩ ▹ Γ ⊢ᵀ σ)
    → (ρ₀ : Point → TΩ.𝒢.⟦ Γ ⟧)
    → (ρ₁ : 𝓑.𝒢.⟦ Γ ⟧)
    → 𝓡⋆[ Γ ] ρ₀ ρ₁
    → 𝓡[ σ ] (λ α → TΩ.⟦ M ⟧ α (ρ₀ α)) (𝓑.⟦ M ⟧ ρ₁)
  main-lemma zero ρ₀ ρ₁ cr = {!!}
  main-lemma succ ρ₀ ρ₁ cr = {!!}
  main-lemma rec[ σ ] ρ₀ ρ₁ cr = {!!}
  main-lemma (ν i x) ρ₀ ρ₁ cr = {!!}
  main-lemma (ƛ M) ρ₀ ρ₁ cr = {!!}
  main-lemma (M · M₁) ρ₀ ρ₁ cr = {!!}
  main-lemma Ω ρ₀ ρ₁ cr = {!!}

-- ⟓
