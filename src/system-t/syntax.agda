module System-T.Syntax where

open import Prelude.Finite
open import Prelude.Functor
open import Prelude.Monad
open import Prelude.Natural
open import Prelude.Path
open import Prelude.String
open import Prelude.Monoidal hiding (_⇒_; _,_)

import Context as Ctx
open Ctx hiding (⋄; _,_)

data BaseType : Set where
  nat atom : BaseType

data Type : Set where
  `_ : BaseType → Type
  _⇒_ : Type → Type → Type

infixr 6 _⇒_

Ctx : Nat → Set
Ctx n = Type ^ n

module 𝔏 where
  data Ob : Set where
    T : Ob
    TΩ : Ob

  data Hom : Ob → Ob → Set where
    T⇒T : Hom T T
    -⇒TΩ : ∀ {𝔏} → Hom 𝔏 TΩ

open 𝔏 using (T; TΩ; T⇒T; -⇒TΩ)

module _ where
  open Ctx
  data _▹_⊢ᵀ_ {n : Nat} : (𝔏 : 𝔏.Ob) (Γ : Ctx n) → Type → Set where
    tok : ∀ {𝔏} {Γ : Ctx n} → String → 𝔏 ▹ Γ ⊢ᵀ ` atom
    zero : ∀ {𝔏} {Γ : Ctx n} → 𝔏 ▹ Γ ⊢ᵀ ` nat
    succ : ∀ {𝔏} {Γ : Ctx n} → 𝔏 ▹ Γ ⊢ᵀ ` nat ⇒ ` nat
    rec[_] : ∀ {𝔏} {Γ : Ctx n} σ → 𝔏 ▹ Γ ⊢ᵀ (` nat ⇒ σ ⇒ σ) ⇒ σ ⇒ ` nat ⇒ σ
    ν : ∀ {𝔏} {Γ : Ctx n} i → 𝔏 ▹ Γ ⊢ᵀ Γ [ i ]
    ƛ_ : ∀ {𝔏} {Γ : Ctx n} {σ τ} → 𝔏 ▹ Γ , σ ⊢ᵀ τ → 𝔏 ▹ Γ ⊢ᵀ σ ⇒ τ
    _·_ : ∀ {𝔏} {Γ : Ctx n} {σ τ} → 𝔏 ▹ Γ ⊢ᵀ (σ ⇒ τ) → 𝔏 ▹ Γ ⊢ᵀ σ → 𝔏 ▹ Γ ⊢ᵀ τ
    Ω : {Γ : Ctx n} → TΩ ▹ Γ ⊢ᵀ ` nat ⇒ ` nat

  infixl 1 _·_
  infixr 3 _▹_⊢ᵀ_

_⊢ᵀ_ : {n : Nat} → Ctx n → Type → Set
Γ ⊢ᵀ τ = ∀ {𝔏} → 𝔏 ▹ Γ ⊢ᵀ τ

⊢ᵀ_ : Type → Set
⊢ᵀ τ = ∀ {n} {Γ : Ctx n} → Γ ⊢ᵀ τ

infixr 3 _⊢ᵀ_
infixr 3 ⊢ᵀ_

⊢ᵀ-map : ∀ {𝔏₀ 𝔏₁ n τ} {Γ : Ctx n} → 𝔏.Hom 𝔏₀ 𝔏₁ → 𝔏₀ ▹ Γ ⊢ᵀ τ → 𝔏₁ ▹ Γ ⊢ᵀ τ
⊢ᵀ-map T⇒T tm = tm
⊢ᵀ-map -⇒TΩ (tok x) = tok x
⊢ᵀ-map -⇒TΩ zero = zero
⊢ᵀ-map -⇒TΩ succ = succ
⊢ᵀ-map -⇒TΩ rec[ σ ] = rec[ σ ]
⊢ᵀ-map -⇒TΩ (ν i) = ν i
⊢ᵀ-map -⇒TΩ (ƛ e) = ƛ ⊢ᵀ-map -⇒TΩ e
⊢ᵀ-map -⇒TΩ (f · m) = ⊢ᵀ-map -⇒TΩ f · ⊢ᵀ-map -⇒TΩ m
⊢ᵀ-map -⇒TΩ Ω = Ω

module _ where
  open Ctx

  ren : ∀ {𝔏 m n τ} {Γ : Ctx m} {Δ : Ctx n} → Ren Γ Δ → 𝔏 ▹ Γ ⊢ᵀ τ → 𝔏 ▹ Δ ⊢ᵀ τ
  ren ρ (tok x) = tok x
  ren ρ zero = zero
  ren ρ succ = succ
  ren ρ rec[ σ ] = rec[ σ ]
  ren ρ (ν i) rewrite Ren.coh ρ i = ν (Ren.ap ρ i)
  ren ρ (ƛ t) = ƛ (ren (ren-extend ρ) t)
  ren ρ (m · n) = ren ρ m · ren ρ n
  ren ρ Ω = Ω

  wk : ∀ {𝔏 n σ τ} {Γ : Ctx n} → 𝔏 ▹ Γ ⊢ᵀ τ → 𝔏 ▹ Γ , σ ⊢ᵀ τ
  wk {σ = σ} {Γ = Γ} = ren ρ
    where
      ρ : ∀ {n σ} {Γ : Ctx n} → Ren Γ (Γ , σ)
      Ren.ap ρ i = su i
      Ren.coh ρ _ = refl
