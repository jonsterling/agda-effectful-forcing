{-# OPTIONS --without-K #-}

module SystemT.Syntax where

open import Basis

import SystemT.Context as Ctx
open Ctx hiding (⋄; _,_)

data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

infixr 6 _⇒_

Ctx : Nat → Set
Ctx n = Type ^ n

module _ where
  open Ctx

  data _⊢ᵀ_ {n : Nat} : (Γ : Ctx n) → Type → Set where
    zero
      : {Γ : Ctx n}
      → Γ ⊢ᵀ nat

    succ
      : {Γ : Ctx n}
      → Γ ⊢ᵀ nat
      → Γ ⊢ᵀ nat

    rec[_]
      : ∀ {Γ : Ctx n} σ
      → (Γ , nat , σ) ⊢ᵀ σ
      → Γ ⊢ᵀ σ
      → Γ ⊢ᵀ nat
      → Γ ⊢ᵀ σ

    ν
      : ∀ {τ} {Γ : Ctx n} i
      → τ ≡ Γ [ i ]
      → Γ ⊢ᵀ τ

    ƛ_
      : ∀ {Γ : Ctx n} {σ τ}
      → (Γ , σ) ⊢ᵀ τ
      → Γ ⊢ᵀ σ ⇒ τ

    _·_
      : ∀ {Γ : Ctx n} {σ τ}
      → Γ ⊢ᵀ (σ ⇒ τ)
      → Γ ⊢ᵀ σ
      → Γ ⊢ᵀ τ

  infixl 1 _·_
  infixr 3 _⊢ᵀ_

⊢ᵀ_ : Type → Set
⊢ᵀ τ = ∀ {n} {Γ : Ctx n} → Γ ⊢ᵀ τ

infixr 3 ⊢ᵀ_
