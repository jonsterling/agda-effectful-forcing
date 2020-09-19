-- Authors: Darin Morrison, Jon Sterling

module Basis where

open import Agda.Primitive public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat public
open import Agda.Builtin.Bool public
open import Agda.Builtin.List public

record Functor ..{ℓ₀ ℓ₁} (F : Set ℓ₀ → Set ℓ₁) : Set (lsuc ℓ₀ ⊔ ℓ₁) where
  no-eta-equality
  field
    map : ∀ {A B} → (A → B) → (F A → F B)

open Functor ⦃ … ⦄ public

record Monad ..{ℓ₀ ℓ₁} (M : Set ℓ₀ → Set ℓ₁) ⦃ fun : Functor M ⦄ : Set (lsuc ℓ₀ ⊔ ℓ₁) where
  infixr 1 bind
  infixr 1 _=≪_
  infixl 1 _≫=_

  field
    return_
      : ∀ {A}
      → (a : A)
      → M A
    bind
      : ∀ {A B}
      → (k : A → M B)
      → (m : M A)
      → M B

  _=≪_
    : ∀ {A B}
    → (k : A → M B)
    → (m : M A)
    → M B
  _=≪_ = bind

  _≫=_
    : ∀ {A B}
    → (m : M A)
    → (k : A → M B)
    → M B
  m ≫= k = bind k m

  syntax bind (λ x → v) m = x ← m ▸ v

open Monad ⦃ … ⦄ public

_∘_
  : ∀ ..{ℓ₀ ℓ₁ ℓ₂}
  → {A : Set ℓ₀} {B : A → Set ℓ₁} {C : ∀ {a} → B a → Set ℓ₂}
  → (g : ∀ {a} → (b : B a) → C b)
  → (f : (a : A) → B a)
  → ((a : A) → C (f a))
(g ∘ f) x = g (f x)

infixr 1 _∘_


module ≡ where
  cmp
    : ∀ {ℓ}
    → {A : Set ℓ}
    → {a b c : A}
    → b ≡ c
    → a ≡ b
    → a ≡ c
  cmp refl refl = refl

  seq
    : ∀ {ℓ}
    → {A : Set ℓ}
    → {a b c : A}
    → a ≡ b
    → b ≡ c
    → a ≡ c
  seq refl refl = refl

  inv
    : ∀ {ℓ} {A : Set ℓ} {a b : A}
    → a ≡ b
    → b ≡ a
  inv refl = refl


  _▪_ = cmp
  infixr 1 _▪_

  _⁻¹ : _
  _⁻¹ = inv


  ap¹
    : ∀ {ℓ₀ ℓ₁}
    → {A : Set ℓ₀} {B : Set ℓ₁}
    → ∀ {a₀ a₁}
    → (F : A → B)
    → a₀ ≡ a₁
    → F a₀ ≡ F a₁
  ap¹ F refl = refl

  coe*
    : ∀ {ℓ₀ ℓ₁}
    → ∀ {A : Set ℓ₀} {a b}
    → (Ψ : A → Set ℓ₁)
    → (ρ : a ≡ b)
    → Ψ a
    → Ψ b
  coe* Ψ refl x = x



module Fin where
  data Fin : (n : Nat) → Set where
    zero
      : ∀ {n}
      → Fin (suc n)
    suc
      : ∀ {n}
      → (i : Fin n)
      → Fin (suc n)

  ⊆nat : ∀ {n} → Fin n → Nat
  ⊆nat zero = zero
  ⊆nat (suc i) = suc (⊆nat i)

open Fin public
  hiding (module Fin)
  using (Fin)
  using (zero; suc)
