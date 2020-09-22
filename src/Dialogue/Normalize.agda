{-# OPTIONS --without-K #-}

module Dialogue.Normalize where

open import Basis

import Dialogue.Core as Core
open Core hiding (module ⊢)

private
  _⌢_ : {Y : Set} → List Y → Y → List Y
  [] ⌢ x = x ∷ []
  (x ∷ xs) ⌢ y = x ∷ (xs ⌢ y)


-- We first define mutually inductive judgments which specify when an
-- Escardó dialogue is normalizable into a Brouwerian mental construction.
module _ {Y Z : Set} where
  mutual
    data _⊩_norm (U : List Y) : 𝔈 Nat Y Z → Set where
      norm-η
        : ∀ x
        → U ⊩ η x norm

      norm-ϝ
        : ∀ {i m}
        → U ⊩?⟨ i ⟩ m norm⊣ U
        → U ⊩ ?⟨ i ⟩ m norm

    data _⊩?⟨_⟩_norm⊣_ (U : List Y) : Nat → (Y → 𝔈 Nat Y Z) → List Y → Set where
      norm-ϝ-cons-ze
        : ∀ {V x m}
        → U ⊩ m x norm
        → U ⊩?⟨ 0 ⟩ m norm⊣ (x ∷ V)

      norm-ϝ-cons-su
        : ∀ {V x i m}
        → U ⊩?⟨ i ⟩ m norm⊣ V
        → U ⊩?⟨ suc i ⟩ m norm⊣ (x ∷ V)

      norm-ϝ-nil-ze
        : ∀ {m}
        → (∀ x → (U ⌢ x) ⊩ m x norm)
        → U ⊩?⟨ 0 ⟩ m norm⊣ []

      norm-ϝ-nil-su
        : ∀ {i m}
        → (∀ x → (U ⌢ x) ⊩?⟨ i ⟩ m norm⊣ [])
        → U ⊩?⟨ suc i ⟩ m norm⊣ []



private
  variable
    Y Z : Set
    U V : List Y


-- Next, we show that the proof-theoretic characterization of
-- tree normalizability was sound, i.e. that whenever the judgment
-- holds for an Escardó dialogue, we can compute the corresponding
-- Brouwerian mental construction.
mutual
  reify
    : {m : 𝔈 Nat Y Z}
    → U ⊩ m norm
    → 𝔅 Y Z
  reify (norm-η x) =
    η x

  reify (norm-ϝ p) =
    reify-ϝ p

  reify-ϝ
    : {m : Y → 𝔈 Nat Y Z}
    → {i : Nat}
    → U ⊩?⟨ i ⟩ m norm⊣ V
    → 𝔅 Y Z

  reify-ϝ (norm-ϝ-cons-ze p) =
    reify p

  reify-ϝ (norm-ϝ-cons-su p) =
    reify-ϝ p

  reify-ϝ (norm-ϝ-nil-ze p) =
    ϝ (reify ∘ p)

  reify-ϝ (norm-ϝ-nil-su p) =
    ϝ (reify-ϝ ∘ p)



-- Then, we show that the proof theory is complete: that for any Escardó dialogue,
-- we can show that it is normalizable.
mutual
  reflect
    : (m : 𝔈 Nat Y Z)
    → U ⊩ m norm
  reflect (η x) =
    norm-η x

  reflect (?⟨ i ⟩ m) =
    norm-ϝ (reflect-ϝ _ i m)

  reflect-ϝ
    : (V : _)
    → (i : Nat)
    → (m : Y → 𝔈 Nat Y Z)
    → U ⊩?⟨ i ⟩ m norm⊣ V

  reflect-ϝ [] zero m =
    norm-ϝ-nil-ze λ x →
      reflect (m x)

  reflect-ϝ [] (suc i) m =
    norm-ϝ-nil-su λ x →
      reflect-ϝ _ i m

  reflect-ϝ (x ∷ V) zero m =
    norm-ϝ-cons-ze (reflect (m x))

  reflect-ϝ (x ∷ V) (suc i) m =
    norm-ϝ-cons-su (reflect-ϝ V i m)

reflect₀ : (m : 𝔈 Nat Y Z) → [] ⊩ m norm
reflect₀ = reflect

norm : 𝔈 Nat Y Z → 𝔅 Y Z
norm = reify ∘ reflect₀


module ⊢ where
  import Spread.Core as 𝔖

  private
    _<++_ : List Y → 𝔖.Point Y → 𝔖.Point Y
    [] <++ α = α
    ((x ∷ xs) <++ α) zero = x
    ((x ∷ xs) <++ α) (suc i) = (xs <++ α) i

    prepend-snoc-id
      : (U : List Y)
      → (α : 𝔖.Point Y)
      → ∀ i → (U <++ α) i ≡ ((U ⌢ α 0) <++ (α ∘ suc)) i
    prepend-snoc-id [] α zero = refl
    prepend-snoc-id [] α (suc i) = refl
    prepend-snoc-id (x ∷ U) α zero = refl
    prepend-snoc-id (x ∷ U) α (suc i) = prepend-snoc-id U α i

  module Coh where
    mutual
      coh
        : (m : 𝔈 Nat Y Z)
        → (p : U ⊩ m norm)
        → (α : 𝔖.Point Y)
        → 𝔈[ m ⋄ (U <++ α) ] ≡ 𝔅[ reify p ⋄ α ]
      coh .(η x) (norm-η x) α = refl
      coh _ (norm-ϝ p) = coh-ϝ _ _ _ _ p

      coh-ϝ
        : (U : _) (V : _)
        → (i : Nat)
        → (m : Y → 𝔈 Nat Y Z)
        → (p : U ⊩?⟨ i ⟩ m norm⊣ V)
        → (α : 𝔖.Point Y)
        → 𝔈[ m ((V <++ α) i) ⋄ (U <++ α) ] ≡ 𝔅[ reify-ϝ p ⋄ α ]

      coh-ϝ U (x ∷ V) .0 m (norm-ϝ-cons-ze p) α =
        coh (m x) p α

      coh-ϝ U (x ∷ V) (suc i) m (norm-ϝ-cons-su p) α =
        coh-ϝ U V i m p α

      coh-ϝ U .[] .0 m (norm-ϝ-nil-ze p) α =
        ≡.seq
         (Core.⊢.⋄-extensional (m _) (prepend-snoc-id U α))
         (coh (m _) (p _) (α ∘ suc))

      coh-ϝ U .[] (suc i) m (norm-ϝ-nil-su p) α =
        ≡.seq
         (Core.⊢.⋄-extensional (m _) (prepend-snoc-id U α))
         (coh-ϝ _ _ i m (p _) (α ∘ suc))


  coh
    : (m : 𝔈 Nat Y Z)
    → (α : 𝔖.Point Y)
    → 𝔈[ m ⋄ α ] ≡ 𝔅[ norm m ⋄ α ]
  coh m =
    Coh.coh m
      (reflect m)
