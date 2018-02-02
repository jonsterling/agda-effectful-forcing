module SystemT.Semantics where

open import Basis

import SystemT.Context as Ctx
open Ctx hiding (⋄; _,_)

import Spread.Baire
import Dialogue as 𝓓

open import SystemT.Syntax

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
    (ρ , x) zero = x
    (ρ , x) (suc i) = ρ i

    infixl 5 _,_

rec : {X : Set} → (Nat → X → X) → X → Nat → X
rec f x zero = x
rec f x (suc n) = f n (rec f x n)

module T where
  open Predicates id public

  ⟦_⟧
    : ∀ {n τ} {Γ : Ctx n}
    → Γ ⊢ᵀ τ
    → 𝒢.⟦ Γ ⟧
    → 𝒱.⟦ τ ⟧
  ⟦ zero ⟧ _ = zero
  ⟦ succ m ⟧ ρ = suc (⟦ m ⟧ ρ)
  ⟦ rec[ σ ] s z n ⟧ ρ = rec (λ x y → ⟦ s ⟧ (ρ 𝒢., x 𝒢., y )) (⟦ z ⟧ ρ) (⟦ n ⟧ ρ)
  ⟦ ν i p ⟧ ρ rewrite p = ρ i
  ⟦ ƛ t ⟧ ρ = λ x → ⟦ t ⟧ (ρ 𝒢., x)
  ⟦ m · n ⟧ ρ = ⟦ m ⟧ ρ (⟦ n ⟧ ρ)

  ⟦_⟧₀
    : ∀ {τ}
    → Ctx.⋄ ⊢ᵀ τ
    → 𝒱.⟦ τ ⟧
  ⟦ t ⟧₀ = ⟦ t ⟧ 𝒢.⋄

module 𝓑 where
  open Spread.Baire
  open Predicates (𝓓.𝔈 Nat Nat) public

  Ext[_]
    : {X : Set} (τ : Type)
    → (X → 𝒱.⟦ τ ⟧)
    → 𝓓.𝔈 Nat Nat X
    → 𝒱.⟦ τ ⟧
  Ext[ ` 𝔟 ] f x =
    x ≫= f
  Ext[ σ ⇒ τ ] g 𝓭 s =
    Ext[ τ ] (λ x → g x s) 𝓭

  ⟦_⟧
    : ∀ {n τ} {Γ : Ctx n}
    → Γ ⊢ᵀ τ
    → 𝒢.⟦ Γ ⟧
    → 𝒱.⟦ τ ⟧
  ⟦ zero ⟧ ρ = 𝓓.η zero
  ⟦ succ m ⟧ ρ = map suc (⟦ m ⟧ ρ)
  ⟦ rec[ σ ] s z n ⟧ ρ =
    Ext[ σ ]
      (rec (λ x y → ⟦ s ⟧ (ρ 𝒢., 𝓓.η x 𝒢., y)) (⟦ z ⟧ ρ))
      (⟦ n ⟧ ρ)
  ⟦ ν x p ⟧ ρ rewrite p = ρ x
  ⟦ ƛ t ⟧ ρ = λ x → ⟦ t ⟧ (ρ 𝒢., x)
  ⟦ m · n ⟧ ρ = ⟦ m ⟧ ρ (⟦ n ⟧ ρ)

  ⟦_⟧₀
    : ∀ {τ}
    → Ctx.⋄ ⊢ᵀ τ
    → 𝒱.⟦ τ ⟧
  ⟦ t ⟧₀ =
    ⟦ t ⟧ 𝒢.⋄

open Spread.Baire

module ⊢ where
  open 𝓓

  𝓡[_]
    : (σ : Type)
    → (α : Point)
    → T.𝒱.⟦ σ ⟧
    → 𝓑.𝒱.⟦ σ ⟧
    → Set

  𝓡[ ` 𝔟 ] α F 𝓭 =
    F ≡ 𝓭 ⋄ α

  𝓡[ σ ⇒ τ ] α F 𝓭 =
    (G : T.𝒱.⟦ σ ⟧)
    (𝓮 : 𝓑.𝒱.⟦ σ ⟧)
      → 𝓡[ σ ] α G 𝓮
      → 𝓡[ τ ] α (F G) (𝓭 𝓮)



  𝓡⋆[_]
    : {n : Nat}
    → (Γ : Ctx n)
    → (α : Point)
    → T.𝒢.⟦ Γ ⟧
    → 𝓑.𝒢.⟦ Γ ⟧
    → Set
  𝓡⋆[ Γ ] α ρ₀ ρ₁ =
    (i : Fin _)
      → 𝓡[ Γ Ctx.[ i ] ] α (ρ₀ i) (ρ₁ i)



  𝓡[_]-Ext-lemma
    : {𝔟 : BaseType}
    → (σ : Type)
    → {α : Point}
    → {F[_] : T.𝒱.⟦ 𝔟 ⟧₀ → T.𝒱.⟦ σ ⟧}
    → {𝓭[_] : 𝓑.𝒱.⟦ 𝔟 ⟧₀ → 𝓑.𝒱.⟦ σ ⟧}
    → (∀ k → 𝓡[ σ ] α F[ k ] 𝓭[ k ])
    → {G : T.𝒱.⟦ 𝔟 ⟧₀}
    → (𝓷 : 𝓑.𝒱.⟦ ` 𝔟 ⟧)
    → 𝓡[ ` 𝔟 ] α G 𝓷
    → 𝓡[ σ ] α F[ G ] (𝓑.Ext[ σ ] 𝓭[_] 𝓷)

  𝓡[ ` 𝔟 ]-Ext-lemma F∼G 𝓷 G∼𝓷 =
    ⊢.⋄-commutes-with-≫= 𝓷 _
      ≡.▪ ≡.ap¹ _ G∼𝓷
      ≡.▪ F∼G _

  𝓡[ σ ⇒ τ ]-Ext-lemma F~G 𝓷 G~𝓷 H 𝓮 H~𝓮 =
    𝓡[ τ ]-Ext-lemma
      (λ k → F~G k H 𝓮 H~𝓮)
      𝓷
      G~𝓷



  -- Using our family of logical relations, we prove that the non-standard
  -- dialogue interpretation of System T coheres with the standard interpretation.
  soundness
    : {n : Nat}
    → {Γ : Ctx n}
    → {σ : Type}
    → (α : Point)
    → (M : Γ ⊢ᵀ σ)
    → {ρ₀ : T.𝒢.⟦ Γ ⟧}
    → {ρ₁ : 𝓑.𝒢.⟦ Γ ⟧}
    → 𝓡⋆[ Γ ] α ρ₀ ρ₁
    → 𝓡[ σ ] α (T.⟦ M ⟧ ρ₀) (𝓑.⟦ M ⟧ ρ₁)

  soundness _ zero ρ₀~ρ₁ =
    refl

  soundness _ (succ m) ρ₀~ρ₁ rewrite soundness _ m  ρ₀~ρ₁ =
    ⊢.⋄-natural suc (𝓑.⟦ m ⟧ _) _

  soundness _ (rec[ σ ] s z n) ρ₀∼ρ₁ =
    𝓡[ σ ]-Ext-lemma R∼𝓻 _ (soundness _ n ρ₀∼ρ₁)

    where
      S = λ x y → T.⟦ s ⟧ (_ T.𝒢., x T.𝒢., y)
      𝓼 = λ x y → 𝓑.⟦ s ⟧ (_ 𝓑.𝒢., x 𝓑.𝒢., y)

      S∼𝓼 : 𝓡[ ` nat ⇒ σ ⇒ σ ] _ S 𝓼
      S∼𝓼 G 𝓮 G∼𝓮 G′ 𝓮′ G′∼𝓮′ =
        soundness _ s λ {
          zero → G′∼𝓮′ ;
          (suc zero) → G∼𝓮 ;
          (suc (suc i)) → ρ₀∼ρ₁ i
        }

      R : Nat → T.𝒱.⟦ σ ⟧
      R k = rec S (T.⟦ z ⟧ _) k

      𝓻 : Nat → 𝓑.𝒱.⟦ σ ⟧
      𝓻 k = rec (𝓼 ∘ η_) (𝓑.⟦ z ⟧ _) k

      R∼𝓻 : (k : Nat) → 𝓡[ σ ] _ (R k) (𝓻 k)
      R∼𝓻 zero = soundness _ z ρ₀∼ρ₁
      R∼𝓻 (suc k) = S∼𝓼 k (η k) refl (R k) (rec (𝓼 ∘ η_) (𝓑.⟦ z ⟧ _) k) (R∼𝓻 k)

  soundness _ (ν i p) ρ₀~ρ₁ rewrite p =
    ρ₀~ρ₁ i

  soundness _ (ƛ M) ρ₀~ρ₁ G 𝓮 G~𝓮 =
    soundness _ M λ
      { zero → G~𝓮
      ; (suc i) → ρ₀~ρ₁ i
      }

  soundness _ (M · N) ρ₀~ρ₁ =
    soundness _ M ρ₀~ρ₁
      (T.⟦ N ⟧ _)
      (𝓑.⟦ N ⟧ _)
      (soundness _ N ρ₀~ρ₁)

  soundness₀
    : {𝔟 : _}
    → (α : Point)
    → (M : Ctx.⋄ ⊢ᵀ ` 𝔟)
    → T.⟦ M ⟧₀ ≡ 𝓑.⟦ M ⟧₀ ⋄ α
  soundness₀ _ M =
    soundness _ M (λ ())
