-- Authors: Darin Morrison, Jon Sterling

{-# OPTIONS --without-K #-}


module Basis where

open import Agda.Primitive public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Nat renaming (Nat to ℕ) public
open import Agda.Builtin.Bool public
open import Agda.Builtin.List public


private
  variable
    ℓ ℓ′ ℓ′′ : Level

postulate
  depfunext : {A : Set ℓ} {B : A → Set ℓ′} {f g : (x : A) → B x} (h : ∀ x → f x ≡ g x) → f ≡ g

funext : {A : Set ℓ} {B : Set ℓ′} {f g : A → B} (h : ∀ x → f x ≡ g x) → f ≡ g
funext = depfunext


_∘_
  : {A : Set ℓ} {B : A → Set ℓ′} {C : ∀ {a} → B a → Set ℓ′′}
  → (g : ∀ {a} → (b : B a) → C b)
  → (f : (a : A) → B a)
  → ((a : A) → C (f a))
(g ∘ f) x = g (f x)

infixr 1 _∘_




module ≡ where
  private
    variable
      A : Set ℓ

  seq
    : {a b c : A}
    → a ≡ b
    → b ≡ c
    → a ≡ c
  seq refl refl = refl

  inv
    : {a b : A}
    → a ≡ b
    → b ≡ a
  inv refl = refl

  cong
    : {B : Set ℓ′}
    → ∀ {a₀ a₁}
    → (F : A → B)
    → a₀ ≡ a₁
    → F a₀ ≡ F a₁
  cong F refl = refl

  coe*
    : {a b : A}
    → (Ψ : A → Set ℓ′)
    → (ρ : a ≡ b)
    → Ψ a
    → Ψ b
  coe* Ψ refl x = x

  coe
    : {B : Set ℓ}
    → A ≡ B
    → A
    → B
  coe refl x = x

  ind : {x : A} (P : (y : A) → x ≡ y → Set ℓ′) → P x refl → {y : A} (x≡y : x ≡ y) → P y x≡y
  ind P p refl = p

  use_by_∎
    : {B : Set ℓ}
    → A
    → A ≡ B
    → B
  use a by p ∎ = coe p a


module Fin where
  data Fin : (n : ℕ) → Set where
    zero
      : ∀ {n}
      → Fin (suc n)
    suc
      : ∀ {n}
      → (i : Fin n)
      → Fin (suc n)

  ⊆nat : ∀ {n} → Fin n → ℕ
  ⊆nat zero = zero
  ⊆nat (suc i) = suc (⊆nat i)

open Fin public
  hiding (module Fin)
  using (Fin)
  using (zero; suc)



private
  variable
    A B C : Set ℓ


record Functor (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  no-eta-equality
  field
    map : (A → B) → (F A → F B)
    law/id : (a : F A) → map (λ x → x) a ≡ a
    law/cmp : {f : A → B} {g : B → C} (a : F A) → map (λ x → g (f x)) a ≡ map g (map f a)

open Functor ⦃ … ⦄ public

record Monad (M : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  infixr 1 bind
  infixl 1 _>>=_

  field
    ret : A → M A
    bind : (A → M B) → M A → M B

  _>>=_ : M A → (A → M B) → M B
  m >>= k = bind k m

  join : M (M A) → M A
  join m = m >>= λ x → x

  field
    law/λ : {k : A → M B} {a : A} → (ret a >>= k) ≡ k a
    law/ρ : (m : M A) → (m >>= ret) ≡ m
    law/α : {f : A → M B} {g : B → M C} (m : M A) → ((m >>= f) >>= g) ≡ (m >>= λ x → f x >>= g)


open Monad ⦃ … ⦄ public

instance
  functor-of-monad : {M : Set ℓ → Set ℓ} ⦃ _ : Monad M ⦄ → Functor M
  Functor.map functor-of-monad f = bind (ret ∘ f)
  Functor.law/id functor-of-monad = law/ρ
  Functor.law/cmp functor-of-monad m =
    ≡.inv
     (≡.seq
      (law/α _)
      (≡.cong
       (λ ■ → bind ■ m)
       (funext λ _ →
        law/λ)))
