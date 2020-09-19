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

  record Alg : Set₁ where
    constructor algebra
    field
      car : Set
      alg : 𝓓.𝔈 Nat Nat car → car
      law : ∀ x → alg (𝓓.η x) ≡ x

  F : Set → Alg
  Alg.car (F A) = 𝓓.𝔈 Nat Nat A
  Alg.alg (F A) 𝔞 = 𝔞 ≫= λ x → x
  Alg.law (F A) 𝔞 = {!!}

  U : Alg → Set
  U = Alg.car

  Alg[_⇒_] : Set → Alg → Alg
  Alg.car Alg[ A ⇒ B ] = A → Alg.car B
  Alg.alg Alg[ A ⇒ B ] 𝔣 a = Alg.alg B (map (λ f → f a) 𝔣)
  Alg.law Alg[ A ⇒ B ] = {!!}

  ⟪_⟫ : Type → Alg
  ⟪ ` nat ⟫ = F Nat
  ⟪ σ ⇒ τ ⟫ = Alg[ U ⟪ σ ⟫ ⇒ ⟪ τ ⟫ ]

  cx⟪_⟫ : {n : Nat} → Ctx n → Alg
  Alg.car cx⟪ Γ ⟫ = (i : Fin _) → Alg.car ⟪ Γ Ctx.[ i ] ⟫
  Alg.alg cx⟪ Γ ⟫ 𝔤 i = Alg.alg ⟪ Γ Ctx.[ i ] ⟫ (map (λ g → g i) 𝔤)
  Alg.law cx⟪ Γ ⟫ = {!!}

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


  𝓡[_]-Ext-lemma
    : (σ : Type)
    → {α : Point}
    → {F : T.𝒱.⟦ nat ⟧₀ → T.𝒱.⟦ σ ⟧}
    → {𝓭 : 𝓑.U 𝓑.⟪ ` nat ⟫ → 𝓑.U 𝓑.⟪ σ ⟫}
    → (∀ k → 𝓡[ σ ] α (F k) (𝓭 (η k)))
    → {G : T.𝒱.⟦ nat ⟧₀}
    → (𝓷 : 𝓑.U 𝓑.⟪ ` nat ⟫)
    → 𝓡[ ` nat ] α G 𝓷
    → 𝓡[ σ ] α (F G) (𝓭 𝓷)
  𝓡[ ` nat ]-Ext-lemma {α} {F} {𝓭} F∼G {G} 𝓷 G∼𝓷 =
    ≡.seq (F∼G G) {!!}
--    ≡.seq (F∼G G) {!!} -- (≡.ap¹ (λ x → 𝔈[ x ⋄ α ]) {!!})
  𝓡[ σ ⇒ τ ]-Ext-lemma {α} {F} {𝓭} F∼G {G} 𝓷 G∼𝓷 H 𝓮 H∼𝓮 = 𝓡[ τ ]-Ext-lemma {α} {λ x → F x H} {λ x → 𝓭 x 𝓮} (λ k → F∼G k H 𝓮 H∼𝓮) 𝓷 G∼𝓷





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
      𝓡[ τ ]-Ext-lemma {α} {R} {𝓻} R∼𝓻 ⟪n⟫ (soundness α n ρ₀∼ρ₁)
--    goal

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

      𝓻 : 𝓑.U 𝓑.⟪ ` nat ⟫ → 𝓑.U 𝓑.⟪ τ ⟫
      𝓻 k = 𝓑.Alg.alg 𝓑.⟪ τ ⟫ (k ≫= rec (λ x₁ x₂ → η (𝓼 (η x₁) (𝓑.Alg.alg 𝓑.⟪ τ ⟫ x₂))) (η (𝓑.tm⟪ z ⟫ ρ₁))) -- rec (𝓼 ∘ η_) ?) --(𝓑.⟦ z ⟧ ρ₁))

      R∼𝓻 : (k : Nat) → 𝓡[ τ ] _ (R k) (𝓻 (η k))
      R∼𝓻 zero rewrite 𝓑.Alg.law 𝓑.⟪ τ ⟫ (𝓑.tm⟪ z ⟫ ρ₁) = soundness _ z ρ₀∼ρ₁
      R∼𝓻 (suc k) = {!S∼𝓼!} --  S∼𝓼 k (η k) refl (R k) (rec (𝓼 ∘ η_) (𝓑.⟦ z ⟧ _) k) (R∼𝓻 k)

{-


      foo : 𝓡[ τ ] _ (R (T.⟦ n ⟧ ρ₀)) (𝓻 (T.⟦ n ⟧ ρ₀))
      foo = R∼𝓻 (T.⟦ n ⟧ ρ₀)
      bar : 𝓡[ ` nat ] α ⟦n⟧ ⟪n⟫
      bar = soundness _ n ρ₀∼ρ₁

      goal4 : (m : _) → 𝓻 m ≡ 𝓑.Alg.alg 𝓑.⟪ τ ⟫ (rec (λ x ih → η (𝓼 (η x) (𝓑.Alg.alg 𝓑.⟪ τ ⟫ ih))) (η (𝓑.tm⟪ z ⟫ ρ₁)) m)
      goal4 zero rewrite 𝓑.Alg.law 𝓑.⟪ τ ⟫ (𝓑.tm⟪ z ⟫ ρ₁) = refl
      goal4 (suc m) rewrite 𝓑.Alg.law 𝓑.⟪ τ ⟫ (𝓼 (η m) (𝓑.Alg.alg 𝓑.⟪ τ ⟫ ((rec (λ x ih → η (𝓼 (η x) (𝓑.Alg.alg 𝓑.⟪ τ ⟫ ih))) (η (𝓑.tm⟪ z ⟫ ρ₁)) m)))) =
        ≡.ap¹ (λ ■ → 𝓑.tm⟪ s ⟫ (ρ₁ 𝓑.⟪,⟫ η m 𝓑.⟪,⟫ ■)) (goal4 m)

      goal5 : {Z : _} (j : _) (𝔪 : Nat → 𝔈 Nat Nat Nat) (f : Nat → 𝔈 Nat Nat Z) → 𝔈[ ?⟨ j ⟩ 𝔪 ⋄ α ] ≡ {!!} → (𝔪 (α j) ≫= f) ≡ (?⟨ j ⟩ 𝔪 ≫= f)
      goal5 = {!!}

      goal3 : (𝔪 : _) → 𝓻 𝔈[ 𝔪 ⋄ α ] ≡ 𝓑.Alg.alg 𝓑.⟪ τ ⟫ (𝔪 ≫= rec (λ x ih → η (𝓼 (η x) (𝓑.Alg.alg 𝓑.⟪ τ ⟫ ih))) (η (𝓑.tm⟪ z ⟫ ρ₁)))
      goal3 (η x) = goal4 x
      goal3 (?⟨ i ⟩ 𝔪) =

        ≡.seq
          (goal3 (𝔪 (α i)))
          {!!}
--          (≡.ap¹
--           (𝓑.Alg.alg 𝓑.⟪ τ ⟫)
--           {!!})

        where
          dream : 𝔪 (α i) ≡ ?⟨ i ⟩ 𝔪
          dream = {!!}

{-
           (≡.seq
            (goal5 i 𝔪 (rec (λ x ih → η 𝓼 (η x) (𝓑.Alg.alg 𝓑.⟪ τ ⟫ ih)) (η 𝓑.tm⟪ z ⟫ ρ₁)))
            {!!}))
-}

      goal2 : 𝓻 ⟦n⟧ ≡ 𝓑.Alg.alg 𝓑.⟪ τ ⟫ (⟪n⟫ ≫= rec (λ x ih → η (𝓼 (η x) (𝓑.Alg.alg 𝓑.⟪ τ ⟫ ih))) (η (𝓑.tm⟪ z ⟫ ρ₁)))
      goal2 rewrite soundness _ n ρ₀∼ρ₁ = goal3 ⟪n⟫


      goal : 𝓡[ τ ] α (R ⟦n⟧) (𝓑.⟦ rec[ τ ] s z n ⟧ ρ₁)
      goal =
        ≡.coe*
         (λ ■ → 𝓡[ τ ] α (R ⟦n⟧) ■)
         goal2
         (R∼𝓻 ⟦n⟧)
-}



  soundness _ (ν i q) ρ₀∼ρ₁ = {!!}
  soundness _ (ƛ t) ρ₀∼ρ₁ = {!!}
  soundness _ (t · t₁) ρ₀∼ρ₁ = {!!}

{-

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
    → T.⟦ M ⟧₀ ≡ 𝔈[ 𝓑.⟦ M ⟧₀ ⋄ α ]
  soundness₀ _ M =
    soundness _ M (λ ())
-}
