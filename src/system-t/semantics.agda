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

open Functor (𝓓.𝓓-functor {Nat})
open Monad (𝓓.𝓓-monad {Nat})

private
  id : {ℓ : _} {A : Set ℓ} → A → A
  id x = x

-- We construct the predicates relative to a functor with which
-- to interpret the base types.
module Predicates (F : Set → Set) where
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
  open Predicates id public

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
  open Predicates id public
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
  open Predicates 𝓓.𝓑 public

  Ext[_]
    : {X : Set} (τ : Type)
    → (X → 𝒱.⟦ τ ⟧)
    → 𝓓.𝓑 X
    → 𝒱.⟦ τ ⟧
  Ext[ ` 𝔟 ] f x =
    x ≫= f
  Ext[ σ ⇒ τ ] g 𝓭 s =
    Ext[ τ ] (λ x → g x s) 𝓭

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
  ⟦ Ω ⟧ ρ = 𝓓.generic

  ⟦_⟧₀
    : ∀ {𝓛 τ}
    → 𝓛 ▹ Ctx.⋄ ⊢ᵀ τ
    → 𝒱.⟦ τ ⟧
  ⟦ t ⟧₀ =
    ⟦ t ⟧ 𝒢.⋄

open Baire

module ⊢ where
  open 𝓓

  𝓡[_]
    : (σ : Type)
    → (Point → TΩ.𝒱.⟦ σ ⟧)
    → 𝓑.𝒱.⟦ σ ⟧
    → Set

  𝓡[ ` 𝔟 ] F[_] 𝓭 =
    (α : Point)
      → F[ α ] ≡ 𝓭 $ α

  𝓡[ σ ⇒ τ ] F[_] 𝓭 =
    (G[_] : Point → TΩ.𝒱.⟦ σ ⟧)
    (𝓮 : 𝓑.𝒱.⟦ σ ⟧)
      → 𝓡[ σ ] G[_] 𝓮
      → 𝓡[ τ ] (λ α → F[ α ] G[ α ]) (𝓭 𝓮)



  𝓡⋆[_]
    : {n : Nat}
    → (Γ : Ctx n)
    → (Point → TΩ.𝒢.⟦ Γ ⟧)
    → 𝓑.𝒢.⟦ Γ ⟧
    → Set
  𝓡⋆[ Γ ] ρ₀ ρ₁ =
    (i : Fin _)
      → 𝓡[ Γ Ctx.[ i ] ] (λ α → ρ₀ α i) (ρ₁ i)



  𝓡[_]-Ext-lemma
    : (σ : Type)
    → (F[_] : Nat → Point → TΩ.𝒱.⟦ σ ⟧)
    → (𝓭[_] : Nat → 𝓑.𝒱.⟦ σ ⟧)
    → (∀ k → 𝓡[ σ ] F[ k ] 𝓭[ k ])
    → (G : Point → Nat)
    → (𝓷 : 𝓑 Nat)
    → 𝓡[ ` nat ] G 𝓷
    → 𝓡[ σ ] (λ α → F[ G α ] α) (𝓑.Ext[ σ ] 𝓭[_] 𝓷)

  𝓡[ ` 𝔟 ]-Ext-lemma F[_] 𝓭[_] F~G G 𝓷 G~𝓷 α =
    F~G (G α) α
      ≡.⟓ ≡.ap¹ (λ k → 𝓭[ k ] $ α) (G~𝓷 α)
      ≡.⟓ ⊢.$-≫= 𝓷 α

  𝓡[ σ ⇒ τ ]-Ext-lemma F[_] 𝓭[_] F~G G 𝓷 G~𝓷 H[_] 𝓮 H~𝓮 =
    𝓡[ τ ]-Ext-lemma
      (λ k α → F[ k ] α H[ α ])
      (λ k → 𝓭[ k ] 𝓮)
      (λ k → F~G k H[_] 𝓮 H~𝓮)
      G
      𝓷
      G~𝓷



  -- Using our family of logical relations, we prove that the non-standard
  -- dialogue interpretation of System T coheres with the standard interpretation.
  soundness
    : {n : Nat}
    → {Γ : Ctx n}
    → {σ : Type}
    → (M : 𝓛.TΩ ▹ Γ ⊢ᵀ σ)
    → (ρ₀ : Point → TΩ.𝒢.⟦ Γ ⟧)
    → (ρ₁ : 𝓑.𝒢.⟦ Γ ⟧)
    → 𝓡⋆[ Γ ] ρ₀ ρ₁
    → 𝓡[ σ ] (λ α → TΩ.⟦ M ⟧ α (ρ₀ α)) (𝓑.⟦ M ⟧ ρ₁)

  soundness zero ρ₀ ρ₁ ρ₀~ρ₁ α =
    refl

  soundness succ ρ₀ ρ₁ ρ₀~ρ₁ n[_] 𝓮 h α rewrite h α =
    ⊢.$-natural su_ 𝓮 α

  soundness rec[ σ ] _ _ _ = lemma
    where
      lemma
        : (S : Point → Nat → TΩ.𝒱.⟦ σ ⟧ → TΩ.𝒱.⟦ σ ⟧)
        → (𝓼 : 𝓑 Nat → 𝓑.𝒱.⟦ σ ⟧ → 𝓑.𝒱.⟦ σ ⟧)
        → 𝓡[ ` nat ⇒ σ ⇒ σ ] S 𝓼
        → (Z : Point → TΩ.𝒱.⟦ σ ⟧)
        → (𝔃 : 𝓑.𝒱.⟦ σ ⟧)
        → 𝓡[ σ ] Z 𝔃
        → (N : Point → Nat)
        → (𝓷 : 𝓑 Nat)
        → 𝓡[ ` nat ] N 𝓷
        → 𝓡[ σ ] (λ α → rec (S α) (Z α) (N α)) (𝓑.Ext[ σ ] (rec (𝓼 ∘ η_) 𝔃) 𝓷)
      lemma S 𝓼 S∼𝓼 Z 𝔃 Z∼𝔃 =
        𝓡[ σ ]-Ext-lemma R 𝓻 R∼𝓻
        where
          R : Nat → Point → TΩ.𝒱.⟦ σ ⟧
          R k α = rec (S α) (Z α) k

          𝓻 : Nat → 𝓑.𝒱.⟦ σ ⟧
          𝓻 k = rec (𝓼 ∘ η_) 𝔃 k

          R∼𝓻 : (k : Nat) → 𝓡[ σ ] (R k) (𝓻 k)
          R∼𝓻 ze = Z∼𝔃
          R∼𝓻 (su_ k) = S∼𝓼 (λ _ → k) (η k) (λ _ → refl) (R k) (𝓻 k) (R∼𝓻 k)

  soundness (ν i p) ρ₀ ρ₁ ρ₀~ρ₁ rewrite p =
    ρ₀~ρ₁ i

  soundness (ƛ M) ρ₀ ρ₁ ρ₀~ρ₁ G[_] 𝓮 G~𝓮 =
    soundness M (λ α → ρ₀ α TΩ.𝒢., G[ α ]) (ρ₁ 𝓑.𝒢., 𝓮) λ
      { ze → G~𝓮
      ; (su i) → ρ₀~ρ₁ i
      }

  soundness (M · N) ρ₀ ρ₁ ρ₀~ρ₁ =
    soundness M ρ₀ ρ₁ ρ₀~ρ₁
      (λ α → TΩ.⟦ N ⟧ α (ρ₀ α))
      (𝓑.⟦ N ⟧ ρ₁)
      (soundness N ρ₀ ρ₁ ρ₀~ρ₁)

  soundness Ω ρ₀ ρ₁ ρ₀~ρ₁ G[_] 𝓮 h α rewrite h α =
    ⊢.$-≫= 𝓮 α


  soundness₀
    : (M : 𝓛.TΩ ▹ Ctx.⋄ ⊢ᵀ ` nat)
    → (α : Point)
    → TΩ.⟦ M ⟧₀ α ≡ 𝓑.⟦ M ⟧₀ $ α
  soundness₀ M =
    soundness M (λ α → TΩ.𝒢.⋄) 𝓑.𝒢.⋄ (λ ())
