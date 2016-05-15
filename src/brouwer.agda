module Brouwer where

open import Prelude.List
open import Prelude.Natural
open import Prelude.Monoidal
open import Prelude.Path
open import Prelude.Functor

open import Dialogue
open import Baire hiding (_⊕<_; prepend; take)

data SnocList (X : Set) : Set where
  [] : SnocList X
  _⌢_ : SnocList X → X → SnocList X

infixl 5 _⌢_

len : {X : Set} → SnocList X → Nat
len [] = 0
len (U ⌢ x) = su (len U)

Neigh : Set
Neigh = SnocList Nat

Species : Set₁
Species = Neigh → Set

data ⊢_◃_ : (U : Neigh) (φ : Species) → Set where
  η : ∀ {φ U} → φ U → ⊢ U ◃ φ
  ζ : ∀ {φ U x} → ⊢ U ◃ φ → ⊢ U ⌢ x ◃ φ
  ϝ : ∀ {φ U} → (∀ x → ⊢ U ⌢ x ◃ φ) → ⊢ U ◃ φ

⊢_bar : (Neigh → Set) → Set
⊢ φ bar = ⊢ [] ◃ φ

data ⊩_◃_ : (U : Neigh) (φ : Species) → Set where
  η : ∀ {φ U} → φ U → ⊩ U ◃ φ
  ϝ : ∀ {φ U} → (∀ x → ⊩ U ⌢ x ◃ φ) → ⊩ U ◃ φ

⊩_bar : Species → Set
⊩ φ bar = ⊩ [] ◃ φ

monotone : Species → Set
monotone φ = ∀ {U x} → φ U → φ (U ⌢ x)

-- Following Brouwer's argument, we can normalize any monotone bar to remove the
-- ζ inferences, which are really just embedded appeals to monotonicity.
module Normalize {φ : Species} (φ-mono : monotone φ) where
  ⊩-mono : monotone (⊩_◃ φ)
  ⊩-mono (η x) = η (φ-mono x)
  ⊩-mono (ϝ κ) = ϝ λ x → ⊩-mono (κ _)

  eval : ∀ {U} → ⊢ U ◃ φ → ⊩ U ◃ φ
  eval (η x) = η x
  eval (ζ p) = ⊩-mono (eval p)
  eval (ϝ κ) = ϝ (λ x → eval (κ x))

  quo : ∀ {U} → ⊩ U ◃ φ → ⊢ U ◃ φ
  quo (η x) = η x
  quo (ϝ κ) = ϝ λ x → quo (κ x)

  norm : ∀ {U} → ⊢ U ◃ φ → ⊢ U ◃ φ
  norm x = quo (eval x)

open Nat using (_+_; _-_)
open List using (_++_)

prepend : Neigh → Point → Point
prepend [] α i = α i
prepend (U ⌢ x) α = prepend U (cons x α)

_⊕<_ : Neigh → Point → Point
U ⊕< α = prepend U α

infixr 4 _⊕<_

{-# DISPLAY prepend U α = U ⊕< α #-}

take : Nat → Point → Neigh
take ze α = []
take (su n) α = (take n α) ⌢ (α n)

_⊨_◃_ : 𝔅ₙ Nat → Neigh → Species → Set
δ ⊨ U ◃ φ =
  (α : Point)
    → φ (take (𝔇ₙ[ δ ] α + len U) (U ⊕< α))

-- δ ⊨ U ◃ φ means that δ computes the securability of U by φ.
_⊨_bar : 𝔅ₙ Nat → Species → Set
δ ⊨ φ bar =
  δ ⊨ [] ◃ φ

𝔇ₙ-map-su : ∀ δ α → 𝔇ₙ[ map su_ δ ] α ≡ su (𝔇ₙ[ δ ] α)
𝔇ₙ-map-su (η x) α = refl
𝔇ₙ-map-su (ϝ κ) α rewrite 𝔇ₙ-map-su (κ (α 0)) (tail α) = refl

_≈_ : Point → Point → Set
α ≈ β = (i : Nat) → α i ≡ β i

cons-expand : Point → Point
cons-expand α = cons (α 0) (tail α)

cons-expansion : ∀ α → cons-expand α ≈ α
cons-expansion α ze = refl
cons-expansion α (su_ n) = refl

cons-cong : ∀ {x y α β} → x ≡ y → α ≈ β → cons x α ≈ cons y β
cons-cong refl q ze = refl
cons-cong refl q (su n) = q n

take-cong : ∀ {α β} m n → m ≡ n → α ≈ β → take m α ≡ take n β
take-cong ze .0 refl q = refl
take-cong (su m) .(su m) refl q rewrite take-cong m _ refl q | q m = refl

--take-cong α β ze p = refl
--take-cong α β (su_ n) p rewrite take-cong α β n p | p n = refl

prepend-cong : ∀ U V α β → U ≡ V → α ≈ β → prepend U α ≈ prepend V β
prepend-cong [] .[] α β refl q = q
prepend-cong (U ⌢ x) .(U ⌢ x) α β refl q = prepend-cong U U (cons x α) (cons x β) refl (cons-cong refl q)

prepend-cons-eq : ∀ U α → (U ⊕< cons (α 0) (tail α)) ≈ (U ⊕< α)
prepend-cons-eq U α = prepend-cong U U (cons (α 0) (tail α)) α refl (cons-expansion α)

take-snoc-tail : ∀ U n α → take n ((U ⌢ α 0) ⊕< tail α) ≡ take n (U ⊕< α)
take-snoc-tail U ze α = refl
take-snoc-tail U (su_ n) α rewrite take-snoc-tail U n α | prepend-cons-eq U α n = refl

module _ {φ : Species} (φ-mono : monotone φ) where

  soundness₁
    : ∀ U
    → ⊩ U ◃ φ
    → 𝔅ₙ Nat
  soundness₁ U (η x) =
    η (len U)
  soundness₁ U (ϝ κ) =
    ϝ λ x →
      soundness₁
        (U ⌢ x)
        (κ x)

{-
  soundness₂
    : ∀ U
    → (p : ⊩ U ◃ φ)
    → soundness₁ U p ⊨ U ◃ φ
  soundness₂ U (η p) α rewrite take-len-prepend U α = p
  soundness₂ U (ϝ κ) α =
    ≡.coe* φ
      (take-snoc-tail-law U α n ≡.⁻¹)
      (soundness₂ (U ⌢ α 0) (κ (α 0)) (tail α))
    where
      δ = soundness₁ (U ⌢ α 0) (κ (α 0))
      n = 𝔇ₙ[ δ ] (tail α)

  soundness
    : ∀ {U}
    → ⊩ U ◃ φ
    → Σ[ 𝔅ₙ Nat ∋ δ ] δ ⊨ U ◃ φ
  soundness p =
    soundness₁ _ p
      ▸ soundness₂ _ p

-}

