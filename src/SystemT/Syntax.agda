module SystemT.Syntax where

open import Prelude.Finite
open import Prelude.Functor
open import Prelude.Monad
open import Prelude.Natural
open import Prelude.Path
open import Prelude.String
open import Prelude.Monoidal hiding (_⇒_; _,_)

import SystemT.Context as Ctx
open Ctx hiding (⋄; _,_)

data BaseType : Set where
  nat : BaseType

data Type : Set where
  `_ : BaseType → Type
  _⇒_ : Type → Type → Type

infixr 6 _⇒_

Ctx : Nat → Set
Ctx n = Type ^ n

module 𝓛 where
  data Ob : Set where
    T : Ob
    TΩ : Ob

  data Hom : Ob → Ob → Set where
    T⇒T : Hom T T
    -⇒TΩ : ∀ {𝔏} → Hom 𝔏 TΩ

open 𝓛 using (T; TΩ; T⇒T; -⇒TΩ)

module _ where
  open Ctx

  data _▹_⊢ᵀ_ {n : Nat} : (𝔏 : 𝓛.Ob) (Γ : Ctx n) → Type → Set where
    zero
      : ∀ {𝓛} {Γ : Ctx n}
      → 𝓛 ▹ Γ ⊢ᵀ ` nat

    succ
      : ∀ {𝓛} {Γ : Ctx n}
      → 𝓛 ▹ Γ ⊢ᵀ ` nat
      → 𝓛 ▹ Γ ⊢ᵀ ` nat

    rec[_]
      : ∀ {𝓛} {Γ : Ctx n} σ
      → 𝓛 ▹ Γ , ` nat , σ ⊢ᵀ σ
      → 𝓛 ▹ Γ ⊢ᵀ σ
      → 𝓛 ▹ Γ ⊢ᵀ ` nat
      → 𝓛 ▹ Γ ⊢ᵀ σ

    ν
      : ∀ {𝓛 τ} {Γ : Ctx n} i
      → τ ≡ Γ [ i ]
      → 𝓛 ▹ Γ ⊢ᵀ τ

    ƛ_
      : ∀ {𝓛} {Γ : Ctx n} {σ τ}
      → 𝓛 ▹ Γ , σ ⊢ᵀ τ
      → 𝓛 ▹ Γ ⊢ᵀ σ ⇒ τ

    _·_
      : ∀ {𝓛} {Γ : Ctx n} {σ τ}
      → 𝓛 ▹ Γ ⊢ᵀ (σ ⇒ τ)
      → 𝓛 ▹ Γ ⊢ᵀ σ
      → 𝓛 ▹ Γ ⊢ᵀ τ

    Ω
      : ∀ {Γ : Ctx n}
      → TΩ ▹ Γ ⊢ᵀ ` nat ⇒ ` nat

  infixl 1 _·_
  infixr 3 _▹_⊢ᵀ_

_⊢ᵀ_ : {n : Nat} → Ctx n → Type → Set
Γ ⊢ᵀ τ = ∀ {𝔏} → 𝔏 ▹ Γ ⊢ᵀ τ

⊢ᵀ_ : Type → Set
⊢ᵀ τ = ∀ {n} {Γ : Ctx n} → Γ ⊢ᵀ τ

infixr 3 _⊢ᵀ_
infixr 3 ⊢ᵀ_

⊢ᵀ-map : ∀ {𝓛₀ 𝓛₁ n τ} {Γ : Ctx n} → 𝓛.Hom 𝓛₀ 𝓛₁ → 𝓛₀ ▹ Γ ⊢ᵀ τ → 𝓛₁ ▹ Γ ⊢ᵀ τ
⊢ᵀ-map T⇒T tm = tm
⊢ᵀ-map -⇒TΩ zero = zero
⊢ᵀ-map -⇒TΩ (succ m) = succ (⊢ᵀ-map -⇒TΩ m)
⊢ᵀ-map -⇒TΩ (rec[ σ ] s z n) = rec[ σ ] (⊢ᵀ-map -⇒TΩ s) (⊢ᵀ-map -⇒TΩ z) (⊢ᵀ-map -⇒TΩ n)
⊢ᵀ-map -⇒TΩ (ν p i) = ν p i
⊢ᵀ-map -⇒TΩ (ƛ e) = ƛ ⊢ᵀ-map -⇒TΩ e
⊢ᵀ-map -⇒TΩ (f · m) = ⊢ᵀ-map -⇒TΩ f · ⊢ᵀ-map -⇒TΩ m
⊢ᵀ-map -⇒TΩ Ω = Ω
