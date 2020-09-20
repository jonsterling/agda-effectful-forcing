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
rec : {X : Set} → (Nat → X → X) → X → Nat → X
rec f x zero = x
rec f x (suc n) = f n (rec f x n)


⟦_⟧ : Type → Set
⟦ nat ⟧ = Nat
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

cx⟦_⟧ : {n : Nat} → Ctx n → Set
cx⟦ Γ ⟧ = (i : Fin _) → ⟦ Γ [ i ] ⟧

⟦⋄⟧ : cx⟦ Ctx.⋄ ⟧
⟦⋄⟧ ()

_⟦,⟧_ : ∀ {n} {Γ : Ctx n} {σ : Type} → cx⟦ Γ ⟧ → ⟦ σ ⟧ → cx⟦ Γ Ctx., σ ⟧
(ρ ⟦,⟧ x) zero = x
(ρ ⟦,⟧ x) (suc i) = ρ i

infixl 5 _⟦,⟧_

tm⟦_⟧
  : ∀ {n τ} {Γ : Ctx n}
  → Γ ⊢ᵀ τ
  → cx⟦ Γ ⟧
  → ⟦ τ ⟧
tm⟦ zero ⟧ _ = zero
tm⟦ succ m ⟧ ρ = suc (tm⟦ m ⟧ ρ)
tm⟦ rec[ σ ] s z n ⟧ ρ = rec (λ x y → tm⟦ s ⟧ (ρ ⟦,⟧ x ⟦,⟧ y )) (tm⟦ z ⟧ ρ) (tm⟦ n ⟧ ρ)
tm⟦ ν i p ⟧ ρ rewrite p = ρ i
tm⟦ ƛ t ⟧ ρ = λ x → tm⟦ t ⟧ (ρ ⟦,⟧ x)
tm⟦ m · n ⟧ ρ = tm⟦ m ⟧ ρ (tm⟦ n ⟧ ρ)

tm⟦_⟧₀
  : ∀ {τ}
  → Ctx.⋄ ⊢ᵀ τ
  → ⟦ τ ⟧
tm⟦ t ⟧₀ = tm⟦ t ⟧ ⟦⋄⟧



𝔈 = 𝓓.𝔈 Nat Nat

record Alg : Set₁ where
  constructor algebra
  field
    car : Set
    alg : 𝔈 car → car
    law/η : ∀ x → alg (𝓓.η x) ≡ x
    law/μ : ∀ (m : 𝔈 (𝔈 car)) → alg (map alg m) ≡ alg (join m)

F : Set → Alg
Alg.car (F A) = 𝔈 A
Alg.alg (F A) 𝔞 = 𝔞 ≫= λ x → x
Alg.law/η (F A) 𝔞 = refl
Alg.law/μ (F A) (𝓓.η x) = refl
Alg.law/μ (F A) (𝓓.?⟨ i ⟩ m) =
  ≡.ap¹ 𝓓.?⟨ i ⟩
   (funext λ x →
    Alg.law/μ (F A) (m x))

U : Alg → Set
U = Alg.car

Alg/Π : (A : Set) → (A → Alg) → Alg
Alg.car (Alg/Π A B) = (x : A) → Alg.car (B x)
Alg.alg (Alg/Π A B) m x = Alg.alg (B x) (map (λ f → f x) m)
Alg.law/η (Alg/Π A B) f = depfunext λ x → Alg.law/η (B x) (f x)
Alg.law/μ (Alg/Π A B) m =
  depfunext λ x →
  ≡.seq
   (≡.ap¹ (Alg.alg (B x))
    (≡.seq
     (≡.inv (law/cmp _ _ m))
     (law/cmp _ _ m)))
   (≡.seq
    (Alg.law/μ (B x) (map (map (λ f → f x)) m))
    (≡.ap¹ (Alg.alg (B x))
     (≡.seq
      (law/α m _ _)
      (≡.inv
       (law/α m _ _)))))


Alg[_⇒_] : Set → Alg → Alg
Alg[ A ⇒ B ] = Alg/Π A λ _ → B

⟪_⟫ : Type → Alg
⟪ nat ⟫ = F Nat
⟪ σ ⇒ τ ⟫ = Alg[ U ⟪ σ ⟫ ⇒ ⟪ τ ⟫ ]

cx⟪_⟫ : {n : Nat} → Ctx n → Alg
cx⟪_⟫ {n} Γ = Alg/Π (Fin n) λ i → ⟪ Γ Ctx.[ i ] ⟫

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

tm⟪_⟫₀
  : ∀ {τ}
  → Ctx.⋄ ⊢ᵀ τ
  → U ⟪ τ ⟫
tm⟪ t ⟫₀ =
  tm⟪ t ⟫ ⟪⋄⟫

open Spread.Baire
open 𝓓 using (𝔈[_⋄_]; η_; ?⟨_⟩)

module Coh where

  _⊨_∋_∼_
    : (α : Point)
    → (σ : Type)
    → (⟦s⟧ : ⟦ σ ⟧)
    → (⟪s⟫ : U ⟪ σ ⟫)
    → Set

  α ⊨ nat ∋ ⟦n⟧ ∼ ⟪n⟫ =
    ⟦n⟧ ≡ 𝔈[ ⟪n⟫ ⋄ α ]

  α ⊨ σ ⇒ τ ∋ ⟦f⟧ ∼ ⟪f⟫ =
    (⟦s⟧ : ⟦ σ ⟧)
    (⟪s⟫ : U ⟪ σ ⟫)
    → α ⊨ σ ∋ ⟦s⟧ ∼ ⟪s⟫
    → α ⊨ τ ∋ ⟦f⟧ ⟦s⟧ ∼ ⟪f⟫ ⟪s⟫

  _⊨cx_∋_∼_
    : {n : Nat}
    → (α : Point)
    → (Γ : Ctx n)
    → (⟦ρ⟧ : cx⟦ Γ ⟧)
    → (⟪ρ⟫ : U cx⟪ Γ ⟫)
    → Set

  α ⊨cx Γ ∋ ⟦ρ⟧ ∼ ⟪ρ⟫ =
    (i : Fin _)
    → α ⊨ Γ Ctx.[ i ] ∋ ⟦ρ⟧ i ∼ ⟪ρ⟫ i

  map-bind-lemma
    : (σ τ : Type)
    → (⟪f⟫ : Nat → U ⟪ σ ⇒ τ ⟫)
    → (⟪n⟫ : 𝔈 Nat)
    → (⟪s⟫ : U ⟪ σ ⟫)
    → (⟪n⟫ ≫= (λ x → η ⟪f⟫ x ⟪s⟫)) ≡ map (λ f → f ⟪s⟫) (⟪n⟫ ≫= (λ x → η ⟪f⟫ x))

  map-bind-lemma _ _ _ (η _) _ =
    refl

  map-bind-lemma σ τ ⟪f⟫ (?⟨ i ⟩ ⟪n⟫) ⟪s⟫ =
    ≡.ap¹ ?⟨ i ⟩
     (funext λ x →
      map-bind-lemma σ τ ⟪f⟫ (⟪n⟫ x) ⟪s⟫)


  lift-sequence
    : (σ : Type)
    → (α : Point)
    → (⟦s⟧ : Nat → ⟦ σ ⟧)
    → (⟪s⟫ : Nat → U ⟪ σ ⟫)
    → ((k : Nat) → α ⊨ σ ∋ ⟦s⟧ k ∼ ⟪s⟫ k)
    → (⟦n⟧ : Nat)
    → (⟪n⟫ : 𝔈 Nat)
    → α ⊨ nat ∋ ⟦n⟧ ∼ ⟪n⟫
    → α ⊨ σ ∋ ⟦s⟧ ⟦n⟧ ∼ Alg.alg ⟪ σ ⟫ (⟪n⟫ ≫= λ n → η ⟪s⟫ n)

  lift-sequence nat α ⟦s⟧ ⟪s⟫ ⟦s⟧∼⟪s⟫ ⟦n⟧ ⟪n⟫ refl rewrite ⟦s⟧∼⟪s⟫ ⟦n⟧ =
    ≡.seq
     (𝓓.⊢.⋄-commutes-with-≫= ⟪n⟫ α)
     (≡.ap¹ (λ ■ → 𝔈[ ■ ⋄ α ])
      (≡.inv
       (Monad.law/α 𝓓.𝔈-monad ⟪n⟫ _ _)))

  lift-sequence (σ ⇒ τ) α ⟦f⟧ ⟪f⟫ ⟦f⟧∼⟪f⟫ ⟦n⟧ ⟪n⟫ ⟦n⟧∼⟪n⟫ ⟦s⟧ ⟪s⟫ ⟦s⟧∼⟪s⟫ =
    ≡.coe*
     (λ ■ → α ⊨ τ ∋ ⟦f⟧ ⟦n⟧ ⟦s⟧ ∼ Alg.alg ⟪ τ ⟫ ■)
     (map-bind-lemma σ τ ⟪f⟫ ⟪n⟫ ⟪s⟫)
     (lift-sequence _ _ _ _
      (λ i → ⟦f⟧∼⟪f⟫ i ⟦s⟧ ⟪s⟫ ⟦s⟧∼⟪s⟫)
      ⟦n⟧ ⟪n⟫ ⟦n⟧∼⟪n⟫)


  -- Using our family of logical relations, we prove that the non-standard
  -- dialogue interpretation of System T coheres with the standard interpretation.
  soundness
    : {n : Nat}
    → {Γ : Ctx n}
    → {σ : Type}
    → (α : Point)
    → (s : Γ ⊢ᵀ σ)
    → (⟦ρ⟧ : cx⟦ Γ ⟧)
    → (⟪ρ⟫ : U cx⟪ Γ ⟫)
    → α ⊨cx Γ ∋ ⟦ρ⟧ ∼ ⟪ρ⟫
    → α ⊨ σ ∋ tm⟦ s ⟧ ⟦ρ⟧ ∼ tm⟪ s ⟫ ⟪ρ⟫

  soundness α zero ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫ =
    refl

  soundness α (succ n) ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫ rewrite soundness _ n _ _ ⟦ρ⟧∼⟪ρ⟫ =
    𝓓.⊢.⋄-natural suc (tm⟪ n ⟫ _) α

  soundness α (rec[ σ ] s z n) ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫ =

    ≡.coe*
     (λ ■ → α ⊨ σ ∋ ⟦rec⟧ ⟦n⟧ ∼ (Alg.alg ⟪ σ ⟫ (Monad.bind 𝓓.𝔈-monad ■ ⟪n⟫)))
     (funext aux)
     (lift-sequence σ α ⟦rec⟧ ⟪rec⟫ ⟦rec⟧∼⟪rec⟫ ⟦n⟧ ⟪n⟫ ⟦n⟧∼⟪n⟫)

    where
      ⟦n⟧ = tm⟦ n ⟧ ⟦ρ⟧
      ⟪n⟫ = tm⟪ n ⟫ ⟪ρ⟫
      ⟦n⟧∼⟪n⟫ = soundness α n ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫

      ⟦z⟧ = tm⟦ z ⟧ ⟦ρ⟧
      ⟪z⟫ = tm⟪ z ⟫ ⟪ρ⟫
      ⟦z⟧∼⟪z⟫ = soundness α z ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫

      ⟦s⟧ = λ x ih → tm⟦ s ⟧ (⟦ρ⟧ ⟦,⟧ x ⟦,⟧ ih)
      ⟪s⟫ = λ x ih → tm⟪ s ⟫ (⟪ρ⟫ ⟪,⟫ x ⟪,⟫ ih)

      ⟦s⟧∼⟪s⟫ =
        λ ⟦x⟧ ⟪x⟫ ⟦x⟧∼⟪x⟫ ⟦ih⟧ ⟪ih⟫ ⟦ih⟧∼⟪ih⟫ →
        soundness α s (⟦ρ⟧ ⟦,⟧ ⟦x⟧ ⟦,⟧ ⟦ih⟧) (⟪ρ⟫ ⟪,⟫ ⟪x⟫ ⟪,⟫ ⟪ih⟫) λ where
          zero → ⟦ih⟧∼⟪ih⟫
          (suc zero) → ⟦x⟧∼⟪x⟫
          (suc (suc i)) → ⟦ρ⟧∼⟪ρ⟫ i

      ⟦rec⟧ = rec ⟦s⟧ ⟦z⟧
      ⟪rec⟫ = rec (λ x ih → ⟪s⟫ (η x) ih) ⟪z⟫

      ⟦rec⟧∼⟪rec⟫ : (k : Nat) → α ⊨ σ ∋ ⟦rec⟧ k ∼ ⟪rec⟫ k
      ⟦rec⟧∼⟪rec⟫ zero rewrite Alg.law/η ⟪ σ ⟫ ⟪z⟫ = ⟦z⟧∼⟪z⟫
      ⟦rec⟧∼⟪rec⟫ (suc k) = ⟦s⟧∼⟪s⟫ k (η k) refl (⟦rec⟧ k) (⟪rec⟫ k) (⟦rec⟧∼⟪rec⟫ k)

      aux : (x : Nat) → 𝓓.η ⟪rec⟫ x ≡ rec (λ x ih → η ⟪s⟫ (η x) (Alg.alg ⟪ σ ⟫ ih)) (η ⟪z⟫) x
      aux zero = refl
      aux (suc x) =
        ≡.ap¹
         (λ ■ → η ⟪s⟫ (η x) ■)
         (≡.inv
          (≡.seq
           (≡.ap¹ (Alg.alg ⟪ σ ⟫) (≡.inv (aux x)))
           (Alg.law/η ⟪ σ ⟫ (⟪rec⟫ x))))


  soundness α (ν i refl) ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫ =
    ⟦ρ⟧∼⟪ρ⟫ i

  soundness α (ƛ f) ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫ ⟦s⟧ ⟪s⟫ ⟦s⟧∼⟪s⟫ =
    soundness α f _ _ λ where
      zero → ⟦s⟧∼⟪s⟫
      (suc i) → ⟦ρ⟧∼⟪ρ⟫ i

  soundness α (s · t) ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫ =
    soundness α s _ _ ⟦ρ⟧∼⟪ρ⟫ _ _
     (soundness α t _ _ ⟦ρ⟧∼⟪ρ⟫)


  soundness₀
    : (α : Point)
    → (n : Ctx.⋄ ⊢ᵀ nat)
    → tm⟦ n ⟧₀ ≡ 𝔈[ tm⟪ n ⟫₀ ⋄ α ]
  soundness₀ _ n =
    soundness _ n _ _ (λ ())
