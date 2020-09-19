module SystemT.Semantics where

open import Basis

import SystemT.Context as Ctx
open Ctx hiding (⋄; _,_)

import Spread.Baire
import Dialogue as 𝓓

open import SystemT.Syntax

postulate funext : {A B : Set} {f g : A → B} (h : ∀ x → f x ≡ g x) → f ≡ g
postulate depfunext : {A : Set} {B : A → Set} {f g : (x : A) → B x} (h : ∀ x → f x ≡ g x) → f ≡ g




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

  record Alg : Set₁ where
    constructor algebra
    field
      car : Set
      alg : 𝓓.𝔈 Nat Nat car → car
      law : ∀ x → alg (𝓓.η x) ≡ x

  F : Set → Alg
  Alg.car (F A) = 𝓓.𝔈 Nat Nat A
  Alg.alg (F A) 𝔞 = 𝔞 ≫= λ x → x
  Alg.law (F A) 𝔞 = refl

  U : Alg → Set
  U = Alg.car

  Alg[_⇒_] : Set → Alg → Alg
  Alg.car Alg[ A ⇒ B ] = A → Alg.car B
  Alg.alg Alg[ A ⇒ B ] 𝔣 a = Alg.alg B (map (λ f → f a) 𝔣)
  Alg.law Alg[ A ⇒ B ] 𝔣 = funext λ x → Alg.law B (𝔣 x)

  ⟪_⟫ : Type → Alg
  ⟪ ` nat ⟫ = F Nat
  ⟪ σ ⇒ τ ⟫ = Alg[ U ⟪ σ ⟫ ⇒ ⟪ τ ⟫ ]

  cx⟪_⟫ : {n : Nat} → Ctx n → Alg
  Alg.car cx⟪ Γ ⟫ = (i : Fin _) → Alg.car ⟪ Γ Ctx.[ i ] ⟫
  Alg.alg cx⟪ Γ ⟫ 𝔤 i = Alg.alg ⟪ Γ Ctx.[ i ] ⟫ (map (λ g → g i) 𝔤)
  Alg.law cx⟪ Γ ⟫ 𝔤 = depfunext λ i → Alg.law ⟪ Γ Ctx.[ i ] ⟫ (𝔤 i)

  _⟪,⟫_ : ∀ {n} {Γ : Ctx n} {σ : Type} → U cx⟪ Γ ⟫ → U ⟪ σ ⟫ → U cx⟪ Γ Ctx., σ ⟫
  (ρ ⟪,⟫ x) zero = x
  (ρ ⟪,⟫ x) (suc i) = ρ i

  infixl 5 _⟪,⟫_

  ⟪⋄⟫ : U cx⟪ Ctx.⋄ ⟫
  ⟪⋄⟫ ()

  tm⟪_⟫
    : ∀ {n τ} {Γ : Ctx n}
    → Γ ⊢ᵀ τ
    → U cx⟪ Γ ⟫
    → U ⟪ τ ⟫
  tm⟪ zero ⟫ ρ = 𝓓.η zero
  tm⟪ succ x ⟫ ρ = map suc (tm⟪ x ⟫ ρ)
  tm⟪ rec[ σ ] s z n ⟫ ρ = Alg.alg ⟪ σ ⟫ (tm⟪ n ⟫ ρ ≫= rec (λ x ih → 𝓓.η (tm⟪ s ⟫ (ρ ⟪,⟫ 𝓓.η x ⟪,⟫ Alg.alg ⟪ σ ⟫ ih))) (𝓓.η (tm⟪ z ⟫ ρ)))
  tm⟪ ν i p ⟫ ρ rewrite p = ρ i
  tm⟪ ƛ t ⟫ ρ x = tm⟪ t ⟫ (ρ ⟪,⟫ x)
  tm⟪ t · u ⟫ ρ = tm⟪ t ⟫ ρ (tm⟪ u ⟫ ρ)

  ⟦_⟧ : ∀ {n τ} {Γ : Ctx n} → Γ ⊢ᵀ τ → U cx⟪ Γ ⟫ → U ⟪ τ ⟫
  ⟦_⟧ = tm⟪_⟫

  ⟦_⟧₀
    : ∀ {τ}
    → Ctx.⋄ ⊢ᵀ τ
    → U ⟪ τ ⟫
  ⟦ t ⟧₀ =
    ⟦ t ⟧ ⟪⋄⟫


open Spread.Baire

module ⊢ where
  open 𝓓

  𝓡[_]
    : (σ : Type)
    → (α : Point)
    → T.𝒱.⟦ σ ⟧
    → 𝓑.U 𝓑.⟪ σ ⟫
    → Set

  𝓡[ ` nat ] α F 𝓭 =
    F ≡ 𝔈[ 𝓭 ⋄ α ]

  𝓡[ σ ⇒ τ ] α F 𝓭 =
    (G : T.𝒱.⟦ σ ⟧)
    (𝓮 : 𝓑.U 𝓑.⟪ σ ⟫)
      → 𝓡[ σ ] α G 𝓮
      → 𝓡[ τ ] α (F G) (𝓭 𝓮)



  𝓡⋆[_]
    : {n : Nat}
    → (Γ : Ctx n)
    → (α : Point)
    → T.𝒢.⟦ Γ ⟧
    → 𝓑.U 𝓑.cx⟪ Γ ⟫
    → Set
  𝓡⋆[ Γ ] α ρ₀ ρ₁ =
    (i : Fin _)
      → 𝓡[ Γ Ctx.[ i ] ] α (ρ₀ i) (ρ₁ i)

  foo : ∀ α 𝓷 (𝓭 : Nat → 𝔈 Nat Nat Nat)→
      𝔈[ 𝓭 𝔈[ 𝓷 ⋄ α ] ⋄ α ] ≡
      𝔈[ Monad.bind 𝔈-monad (λ x → x) (𝓷 ≫= λ x → η 𝓭 x) ⋄ α ]
  foo α (η x) 𝓭 = refl
  foo α (?⟨ i ⟩ 𝓷) 𝓭 =
    foo α (𝓷 (α i)) 𝓭

  xxxx : ∀ σ τ (F : Nat → T.𝒱.⟦ σ ⇒ τ ⟧)
         (𝓭 : Nat → 𝓑.U 𝓑.⟪ σ ⇒ τ ⟫)
         (G : Nat) (𝓷 : 𝔈 Nat Nat Nat)
         (𝓮 : 𝓑.U 𝓑.⟪ σ ⟫) →
       (𝓷 ≫= (λ x → η 𝓭 x 𝓮)) ≡
       map (λ f → f 𝓮) (𝓷 ≫= (λ x → η 𝓭 x))
  xxxx σ τ F 𝓭 G (η x) 𝓮 = refl
  xxxx σ τ F 𝓭 G (?⟨ i ⟩ 𝓷) 𝓮 = ≡.ap¹ ?⟨ i ⟩ (funext (λ x → xxxx σ τ F 𝓭 G (𝓷 x) 𝓮))



  𝓡[_]-Ext-lemma
    : (σ : Type)
    → {α : Point}
    → {F : Nat → T.𝒱.⟦ σ ⟧}
    → {𝓭 : Nat → 𝓑.U 𝓑.⟪ σ ⟫}
    → (∀ k → 𝓡[ σ ] α (F k) (𝓭 k))
    → {G : T.𝒱.⟦ nat ⟧₀}
    → (𝓷 : 𝓑.U 𝓑.⟪ ` nat ⟫)
    → 𝓡[ ` nat ] α G 𝓷
    → 𝓡[ σ ] α (F G) (𝓑.Alg.alg 𝓑.⟪ σ ⟫ (𝓷 ≫= λ x → η (𝓭 x))) -- (𝓷 ≫= 𝓭)
  𝓡[ ` nat ]-Ext-lemma {α} {F} {𝓭} F∼G {G} 𝓷 G∼𝓷 rewrite (F∼G G) | G∼𝓷 =
    foo α 𝓷 𝓭
  𝓡[ σ ⇒ τ ]-Ext-lemma {α} {F} {𝓭} F∼G {G} 𝓷 G∼𝓷 H 𝓮 H∼𝓮 =
    let ih = 𝓡[ τ ]-Ext-lemma {α} {λ x → F x H} {λ x → 𝓭 x 𝓮} (λ k → F∼G k H 𝓮 H∼𝓮) 𝓷 G∼𝓷 in
    ≡.coe* (λ ■ → 𝓡[ τ ] α (F G H) (𝓑.Alg.alg 𝓑.⟪ τ ⟫ ■)) (xxxx σ τ F 𝓭 G 𝓷 𝓮) ih


  -- Using our family of logical relations, we prove that the non-standard
  -- dialogue interpretation of System T coheres with the standard interpretation.
  soundness
    : {n : Nat}
    → {Γ : Ctx n}
    → {σ : Type}
    → (α : Point)
    → (M : Γ ⊢ᵀ σ)
    → {ρ₀ : T.𝒢.⟦ Γ ⟧}
    → {ρ₁ : 𝓑.U 𝓑.cx⟪ Γ ⟫}
    → 𝓡⋆[ Γ ] α ρ₀ ρ₁
    → 𝓡[ σ ] α (T.⟦ M ⟧ ρ₀) (𝓑.⟦ M ⟧ ρ₁)

  soundness _ zero ρ₀∼ρ₁ =
    refl

  soundness _ (succ t) ρ₀∼ρ₁ rewrite soundness _ t ρ₀∼ρ₁ =
    ⊢.⋄-natural suc (𝓑.tm⟪ t ⟫ _) _

  soundness α (rec[ τ ] s z n) {ρ₀} {ρ₁} ρ₀∼ρ₁ =
    let xxx = 𝓡[ τ ]-Ext-lemma {α} {R} {𝓻} R∼𝓻 {T.⟦ n ⟧ (λ i → ρ₀ i)} ⟪n⟫ (soundness α n ρ₀∼ρ₁) in
    ≡.coe*
     (λ ■ → 𝓡[ τ ] α (R ⟦n⟧) (𝓑.Alg.alg 𝓑.⟪ τ ⟫ (Monad.bind 𝔈-monad ■ ⟪n⟫)))
     (funext welp)
     xxx

    where


      ⟦n⟧ = T.⟦ n ⟧ ρ₀
      ⟪n⟫ = 𝓑.⟦ n ⟧ ρ₁

      S = λ x y → T.⟦ s ⟧ (_ T.𝒢., x T.𝒢., y)
      𝓼 = λ x y → 𝓑.⟦ s ⟧ (_ 𝓑.⟪,⟫ x 𝓑.⟪,⟫ y)

      S∼𝓼 : 𝓡[ ` nat ⇒ τ ⇒ τ ] _ S 𝓼
      S∼𝓼 G 𝓮 G∼𝓮 G′ 𝓮′ G′∼𝓮′ =
        soundness _ s λ {
          zero → G′∼𝓮′ ;
          (suc zero) → G∼𝓮 ;
          (suc (suc i)) → ρ₀∼ρ₁ i
        }

      R : Nat → T.𝒱.⟦ τ ⟧
      R k = rec S (T.⟦ z ⟧ ρ₀) k

      𝓻 : Nat → 𝓑.U 𝓑.⟪ τ ⟫
      𝓻 = rec (λ x ih → 𝓼 (η x) ih) (𝓑.tm⟪ z ⟫ ρ₁)

      R∼𝓻 : (k : Nat) → 𝓡[ τ ] _ (R k) (𝓻 k)
      R∼𝓻 zero rewrite 𝓑.Alg.law 𝓑.⟪ τ ⟫ (𝓑.tm⟪ z ⟫ ρ₁) = soundness _ z ρ₀∼ρ₁
      R∼𝓻 (suc k) = S∼𝓼 k (η k) refl (R k) (𝓻 k) (R∼𝓻 k)

      welp : (x : Nat) →  _≡_ {_} {𝔈 Nat Nat _} (𝓓.η 𝓻 x) (rec (λ x ih → 𝓓.η 𝓑.tm⟪ s ⟫ (ρ₁ 𝓑.⟪,⟫ (𝓓.η x) 𝓑.⟪,⟫ 𝓑.Alg.alg 𝓑.⟪ τ ⟫ ih)) (𝓓.η 𝓑.tm⟪ z ⟫ ρ₁) x)
      welp zero = refl
      welp (suc x) =
        ≡.ap¹
         (λ ■ → η (𝓑.tm⟪ s ⟫ (ρ₁ 𝓑.⟪,⟫ η x 𝓑.⟪,⟫ ■)))
         (≡.inv
          (≡.seq
           (≡.ap¹ (𝓑.Alg.alg 𝓑.⟪ τ ⟫) (≡.inv (welp x)))
           (𝓑.Alg.law 𝓑.⟪ τ ⟫ (𝓻 x))))



  soundness _ (ν i q) ρ₀∼ρ₁ rewrite q =
    ρ₀∼ρ₁ i

  soundness _ (ƛ t) ρ₀∼ρ₁ G 𝓮 x =
    soundness _ t λ { zero → x ; (suc i) → ρ₀∼ρ₁ i}

  soundness _ (t · u) ρ₀∼ρ₁ =
    soundness _ t ρ₀∼ρ₁ _ _ (soundness _ u ρ₀∼ρ₁)


  soundness₀
    : (α : Point)
    → (M : Ctx.⋄ ⊢ᵀ ` nat)
    → T.⟦ M ⟧₀ ≡ 𝔈[ 𝓑.⟦ M ⟧₀ ⋄ α ]
  soundness₀ _ M =
    soundness _ M (λ ())
