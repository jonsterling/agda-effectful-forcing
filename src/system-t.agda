module system-t where

open import Prelude.Finite
open import Prelude.Functor
open import Prelude.Monad
open import Prelude.Natural
open import Prelude.String
open import Prelude.Monoidal hiding (_⇒_)

open Π using (_∘_)

open import Baire
open import Dialogue
open import Context

data type : Set where
  nat : type
  atom : type
  _⇒_ : type → type → type

infixr 6 _⇒_

Ctx : Nat → Set
Ctx n = type ^ n

module Lang where
  data Ob : Set where
    T : Ob
    TΩ : Ob

  data Hom : Ob → Ob → Set where
    T⇒T : Hom T T
    -⇒TΩ : ∀ {𝔏} → Hom 𝔏 TΩ

data _▹_⊢ᵀ_ {n : Nat} : (𝔏 : Lang.Ob) (Γ : Ctx n) → type → Set where
  tok : {𝔏 : _} {Γ : Ctx n} → String → 𝔏 ▹ Γ ⊢ᵀ atom
  ze : {𝔏 : _} {Γ : Ctx n} → 𝔏 ▹ Γ ⊢ᵀ nat
  su : {𝔏 : _} {Γ : Ctx n} → 𝔏 ▹ Γ ⊢ᵀ nat ⇒ nat
  rec : {𝔏 : _} {Γ : Ctx n} {σ : type} → 𝔏 ▹ Γ ⊢ᵀ (nat ⇒ σ ⇒ σ) ⇒ σ ⇒ nat ⇒ σ
  ν : {𝔏 : _} {Γ : Ctx n} → (i : Fin n) → 𝔏 ▹ Γ ⊢ᵀ Γ [ i ]
  ƛ_ : {𝔏 : _} {Γ : Ctx n} {σ τ : type} → 𝔏 ▹ Γ , σ ⊢ᵀ τ → 𝔏 ▹ Γ ⊢ᵀ σ ⇒ τ
  _·_ : {𝔏 : _} {Γ : Ctx n} {σ τ : type} → 𝔏 ▹ Γ ⊢ᵀ (σ ⇒ τ) → 𝔏 ▹ Γ ⊢ᵀ σ → 𝔏 ▹ Γ ⊢ᵀ τ
  Ω : {Γ : Ctx n} → Lang.TΩ ▹ Γ ⊢ᵀ nat ⇒ nat

infixr 3 _▹_⊢ᵀ_

⊢ᵀ-map : ∀ {𝔏₀ 𝔏₁ n τ} {Γ : Ctx n} → Lang.Hom 𝔏₀ 𝔏₁ → 𝔏₀ ▹ Γ ⊢ᵀ τ → 𝔏₁ ▹ Γ ⊢ᵀ τ
⊢ᵀ-map Lang.T⇒T tm = tm
⊢ᵀ-map Lang.-⇒TΩ (tok x) = tok x
⊢ᵀ-map Lang.-⇒TΩ ze = ze
⊢ᵀ-map Lang.-⇒TΩ su = su
⊢ᵀ-map Lang.-⇒TΩ rec = rec
⊢ᵀ-map Lang.-⇒TΩ (ν i) = ν i
⊢ᵀ-map Lang.-⇒TΩ (ƛ e) = ƛ ⊢ᵀ-map Lang.-⇒TΩ e
⊢ᵀ-map Lang.-⇒TΩ (f · m) = ⊢ᵀ-map Lang.-⇒TΩ f · ⊢ᵀ-map Lang.-⇒TΩ m
⊢ᵀ-map Lang.-⇒TΩ Ω = Ω

id : {ℓ : _} {A : Set ℓ} → A → A
id x = x

𝒱⟦_⟧ : type → (Set → Set) → Set
𝒱⟦ nat ⟧ f = f Nat
𝒱⟦ atom ⟧ f = f String
𝒱⟦ σ ⇒ τ ⟧ f = 𝒱⟦ σ ⟧ f → 𝒱⟦ τ ⟧ f

𝒢⟦_⟧ : {n : Nat} → Ctx n → (Set → Set) → Set
𝒢⟦ Γ ⟧ f = (i : Fin _) → 𝒱⟦ Γ [ i ] ⟧ f

⟦⋄⟧ : ∀ {f} → 𝒢⟦ ⋄ ⟧ f
⟦⋄⟧ ()

_⟦,⟧_ : ∀ {f n} {Γ : Ctx n} {σ : type} → 𝒢⟦ Γ ⟧ f → 𝒱⟦ σ ⟧ f → 𝒢⟦ Γ , σ ⟧ f
(ρ ⟦,⟧ x) ze = x
(ρ ⟦,⟧ x) (su_ i) = ρ i

Rec : {X : Set} → (Nat → X → X) → X → Nat → X
Rec f x ze = x
Rec f x (su_ n) = f n (Rec f x n)

ext : {X : Set} {τ : type} → (X → 𝒱⟦ τ ⟧ 𝔅) → 𝔅 X → 𝒱⟦ τ ⟧ 𝔅
ext {τ = nat} f x = x ≫= f
ext {τ = atom} f x = x ≫= f
ext {τ = σ ⇒ τ} g δ s = ext {τ = τ} (λ x → g x s) δ

_⊩⟦_⟧_ : ∀ {𝔏 n τ} {Γ : Ctx n} → Point → 𝔏 ▹ Γ ⊢ᵀ τ → 𝒢⟦ Γ ⟧ id → 𝒱⟦ τ ⟧ id
α ⊩⟦ tok x ⟧ ρ = x
α ⊩⟦ ze ⟧ ρ = ze
α ⊩⟦ su ⟧ ρ = su_
α ⊩⟦ rec ⟧ ρ = Rec
α ⊩⟦ ν i ⟧ ρ = ρ i
α ⊩⟦ ƛ e ⟧ ρ = λ x → α ⊩⟦ e ⟧ (ρ ⟦,⟧ x)
α ⊩⟦ m · n ⟧ ρ = (α ⊩⟦ m ⟧ ρ) (α ⊩⟦ n ⟧ ρ)
α ⊩⟦ Ω ⟧ ρ = α

𝔅⟦_⟧ : ∀ {n τ} {Γ : Ctx n} → Lang.TΩ ▹ Γ ⊢ᵀ τ → 𝒢⟦ Γ ⟧ 𝔅 → 𝒱⟦ τ ⟧ 𝔅
𝔅⟦ tok x ⟧ _ = η x
𝔅⟦ ze ⟧ _ = η ze
𝔅⟦ su ⟧ _ = map su_
𝔅⟦ rec {σ = σ} ⟧ _ s z = ext {τ = σ} (Rec (s ∘ η) z)
𝔅⟦ ν i ⟧ ρ = ρ i
𝔅⟦ ƛ e ⟧ ρ = λ x → 𝔅⟦ e ⟧ (ρ ⟦,⟧ x)
𝔅⟦ m · n ⟧ ρ = 𝔅⟦ m ⟧ ρ (𝔅⟦ n ⟧ ρ)
𝔅⟦ Ω ⟧ _ = ext {τ = nat} (ϝ η)

⌈_⌉ : {𝔏 : _} → 𝔏 ▹ ⋄ ⊢ᵀ (nat ⇒ nat) ⇒ nat → 𝔅 Nat
⌈ m ⌉ = 𝔅⟦ ⊢ᵀ-map Lang.-⇒TΩ m · Ω ⟧ ⟦⋄⟧
