-- Authors: Darin Morrison, Jon Sterling

{-# OPTIONS --without-K #-}


module Basis where

open import Agda.Primitive public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat public
open import Agda.Builtin.Bool public
open import Agda.Builtin.List public


private
  variable
    ℓ ℓ′ ℓ′′ : Level

postulate
  depfunext : {A : Set ℓ} {B : A → Set ℓ′} {f g : (x : A) → B x} (h : ∀ x → f x ≡ g x) → f ≡ g

funext : {A : Set ℓ} {B : Set ℓ′} {f g : A → B} (h : ∀ x → f x ≡ g x) → f ≡ g
funext = depfunext


module ≡ where
  cmp
    : {A : Set ℓ}
    → {a b c : A}
    → b ≡ c
    → a ≡ b
    → a ≡ c
  cmp refl refl = refl

  seq
    : {A : Set ℓ}
    → {a b c : A}
    → a ≡ b
    → b ≡ c
    → a ≡ c
  seq refl refl = refl

  inv
    : {A : Set ℓ} {a b : A}
    → a ≡ b
    → b ≡ a
  inv refl = refl


  _▪_ = cmp
  infixr 1 _▪_

  _⁻¹ : _
  _⁻¹ = inv


  cong
    : {A : Set ℓ} {B : Set ℓ′}
    → ∀ {a₀ a₁}
    → (F : A → B)
    → a₀ ≡ a₁
    → F a₀ ≡ F a₁
  cong F refl = refl

  coe*
    : {A : Set ℓ} {a b : A}
    → (Ψ : A → Set ℓ′)
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



record Functor (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  no-eta-equality
  field
    map : ∀ {A B} → (A → B) → (F A → F B)
    law/id : ∀ {A} (a : F A) → map (λ x → x) a ≡ a
    law/cmp : ∀ {A B C} (f : A → B) (g : B → C) (a : F A) → map (λ x → g (f x)) a ≡ map g (map f a)

open Functor ⦃ … ⦄ public

record Monad (M : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  infixr 1 bind
  infixl 1 _>>=_

  field
    ret
      : ∀ {A}
      → (a : A)
      → M A
    bind
      : ∀ {A B}
      → (k : A → M B)
      → (m : M A)
      → M B

  _>>=_
    : ∀ {A B}
    → (m : M A)
    → (k : A → M B)
    → M B
  m >>= k = bind k m

  join : {A : Set ℓ} → M (M A) → M A
  join m = m >>= λ x → x

  field
    law/λ : {A B : Set ℓ} (a : A) (k : A → M B) → (ret a >>= k) ≡ k a
    law/ρ : {A : Set ℓ} (m : M A) → (m >>= ret) ≡ m
    law/α : {A B C : Set ℓ} (m : M A) (f : A → M B) (g : B → M C) → ((m >>= f) >>= g) ≡ (m >>= λ x → f x >>= g)


open Monad ⦃ … ⦄ public

_∘_
  : {A : Set ℓ} {B : A → Set ℓ} {C : ∀ {a} → B a → Set ℓ′′}
  → (g : ∀ {a} → (b : B a) → C b)
  → (f : (a : A) → B a)
  → ((a : A) → C (f a))
(g ∘ f) x = g (f x)

infixr 1 _∘_


instance
  functor-of-monad : {M : Set ℓ → Set ℓ} ⦃ _ : Monad M ⦄ → Functor M
  Functor.map (functor-of-monad {ℓ} {M} ⦃ monad ⦄) f = bind (ret ∘ f)
  Functor.law/id (functor-of-monad {ℓ} {M} ⦃ monad ⦄) = law/ρ
  Functor.law/cmp (functor-of-monad {ℓ} {M} ⦃ monad ⦄) f g m =
    ≡.inv
     (≡.seq
      (law/α m (ret ∘ f) (ret ∘ g))
      (≡.cong
       (λ ■ → bind ■ m)
       (funext λ x →
        law/λ (f x) (ret ∘ g))))
