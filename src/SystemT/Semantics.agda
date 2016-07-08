module SystemT.Semantics where

open import Prelude.Finite
open import Prelude.Functor hiding (map)
open import Prelude.Monad hiding (_≫=_)
open import Prelude.Monoidal hiding (_⇒_; _,_)
open import Prelude.Natural
open import Prelude.String
open import Prelude.Path

import SystemT.Context as Ctx
open Ctx hiding (⋄; _,_)
open Π using (_∘_)

import Spread.Baire
import Dialogue as 𝓓

open import SystemT.Syntax

open Functor (𝓓.𝓓-functor {Nat} {Nat})
open Monad (𝓓.𝓓-monad {Nat} {Nat})

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

    infixl 5 _,_

rec : {X : Set} → (Nat → X → X) → X → Nat → X
rec f x ze = x
rec f x (su n) = f n (rec f x n)

module T where
  open Predicates id public

  ⟦_⟧
    : ∀ {n τ} {Γ : Ctx n}
    → Γ ⊢ᵀ τ
    → 𝒢.⟦ Γ ⟧
    → 𝒱.⟦ τ ⟧
  ⟦ zero ⟧ _ = ze
  ⟦ succ m ⟧ ρ = su (⟦ m ⟧ ρ)
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
    : ∀ {n τ} {Γ : Ctx n}
    → Γ ⊢ᵀ τ
    → 𝒢.⟦ Γ ⟧
    → 𝒱.⟦ τ ⟧
  ⟦ zero ⟧ ρ = 𝓓.η ze
  ⟦ succ m ⟧ ρ = map su_ (⟦ m ⟧ ρ)
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
    F ≡ 𝓭 $ α

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
    → (α : Point)
    → (F[_] : T.𝒱.⟦ 𝔟 ⟧₀ → T.𝒱.⟦ σ ⟧)
    → (𝓭[_] : 𝓑.𝒱.⟦ 𝔟 ⟧₀ → 𝓑.𝒱.⟦ σ ⟧)
    → (∀ k → 𝓡[ σ ] α F[ k ] 𝓭[ k ])
    → (G : T.𝒱.⟦ 𝔟 ⟧₀)
    → (𝓷 : 𝓑.𝒱.⟦ ` 𝔟 ⟧)
    → 𝓡[ ` 𝔟 ] α G 𝓷
    → 𝓡[ σ ] α F[ G ] (𝓑.Ext[ σ ] 𝓭[_] 𝓷)

  𝓡[ ` 𝔟 ]-Ext-lemma α F[_] 𝓭[_] F~G G 𝓷 G~𝓷 =
    F~G G
      ≡.⟓ ≡.ap¹ (λ k → 𝓭[ k ] $ α) G~𝓷
      ≡.⟓ ⊢.$-≫= 𝓷 α

  𝓡[ σ ⇒ τ ]-Ext-lemma α F[_] 𝓭[_] F~G G 𝓷 G~𝓷 H 𝓮 H~𝓮 =
    𝓡[ τ ]-Ext-lemma
      α
      (λ k → F[ k ] H)
      (λ k → 𝓭[ k ] 𝓮)
      (λ k → F~G k H 𝓮 H~𝓮)
      G
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
    → (ρ₀ : T.𝒢.⟦ Γ ⟧)
    → (ρ₁ : 𝓑.𝒢.⟦ Γ ⟧)
    → 𝓡⋆[ Γ ] α ρ₀ ρ₁
    → 𝓡[ σ ] α (T.⟦ M ⟧ ρ₀) (𝓑.⟦ M ⟧ ρ₁)

  soundness α zero ρ₀ ρ₁ ρ₀~ρ₁ =
    refl

  soundness α (succ m) ρ₀ ρ₁ ρ₀~ρ₁ rewrite soundness α m ρ₀ ρ₁ ρ₀~ρ₁ =
    ⊢.$-natural su_ (𝓑.⟦ m ⟧ ρ₁) α

  soundness α (rec[ σ ] s z n) ρ₀ ρ₁ ρ₀∼ρ₁ = 𝓡[ σ ]-Ext-lemma α R 𝓻 R∼𝓻 N 𝓷 N∼𝓷
    where
      S = λ x y → T.⟦ s ⟧ (ρ₀ T.𝒢., x T.𝒢., y)
      𝓼 = λ x y → 𝓑.⟦ s ⟧ (ρ₁ 𝓑.𝒢., x 𝓑.𝒢., y)

      S∼𝓼 : 𝓡[ ` nat ⇒ σ ⇒ σ ] α S 𝓼
      S∼𝓼 G 𝓮 G∼𝓮 G′ 𝓮′ G′∼𝓮′ =
        soundness
          α
          s
          (ρ₀ T.𝒢., G T.𝒢., G′)
          (ρ₁ 𝓑.𝒢., 𝓮 𝓑.𝒢., 𝓮′)
          (λ { ze → G′∼𝓮′ ; (su ze) → G∼𝓮 ; (su (su i)) → ρ₀∼ρ₁ i })

      Z = T.⟦ z ⟧ ρ₀
      𝔃 = 𝓑.⟦ z ⟧ ρ₁
      Z∼𝔃 = soundness α z ρ₀ ρ₁ ρ₀∼ρ₁

      N = T.⟦ n ⟧ ρ₀
      𝓷 = 𝓑.⟦ n ⟧ ρ₁
      N∼𝓷 = soundness α n ρ₀ ρ₁ ρ₀∼ρ₁

      R : Nat → T.𝒱.⟦ σ ⟧
      R k = rec S Z k

      𝓻 : Nat → 𝓑.𝒱.⟦ σ ⟧
      𝓻 k = rec (𝓼 ∘ η_) 𝔃 k

      R∼𝓻 : (k : Nat) → 𝓡[ σ ] α (R k) (𝓻 k)
      R∼𝓻 ze = Z∼𝔃
      R∼𝓻 (su_ k) = S∼𝓼 k (η k) refl (R k) (𝓻 k) (R∼𝓻 k)

  soundness α (ν i p) ρ₀ ρ₁ ρ₀~ρ₁ rewrite p =
    ρ₀~ρ₁ i

  soundness α (ƛ M) ρ₀ ρ₁ ρ₀~ρ₁ G 𝓮 G~𝓮 =
    soundness α M (ρ₀ T.𝒢., G) (ρ₁ 𝓑.𝒢., 𝓮) λ
      { ze → G~𝓮
      ; (su i) → ρ₀~ρ₁ i
      }

  soundness α (M · N) ρ₀ ρ₁ ρ₀~ρ₁ =
    soundness α M ρ₀ ρ₁ ρ₀~ρ₁
      (T.⟦ N ⟧ ρ₀)
      (𝓑.⟦ N ⟧ ρ₁)
      (soundness α N ρ₀ ρ₁ ρ₀~ρ₁)

  soundness₀
    : {𝔟 : _}
    → (α : Point)
    → (M : Ctx.⋄ ⊢ᵀ ` 𝔟)
    → T.⟦ M ⟧₀ ≡ 𝓑.⟦ M ⟧₀ $ α
  soundness₀ α M =
    soundness α M T.𝒢.⋄ 𝓑.𝒢.⋄ (λ ())
