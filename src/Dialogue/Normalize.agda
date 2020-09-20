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
mutual
  data _⊩_norm {Y Z : Set} (U : List Y) : 𝔈 Nat Y Z → Set where
    norm-η
      : ∀ x
      → U ⊩ η x norm

    norm-ϝ
      : ∀ {i m}
      → U ⊩?⟨ i ⟩ m norm⊣ U
      → U ⊩ ?⟨ i ⟩ m norm

  data _⊩?⟨_⟩_norm⊣_ {Y Z : Set} (U : List Y) : Nat → (Y → 𝔈 Nat Y Z) → List Y → Set where
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

-- Next, we show that the proof-theoretic characterization of
-- tree normalizability was sound, i.e. that whenever the judgment
-- holds for an Escardó dialogue, we can compute the corresponding
-- Brouwerian mental construction.
mutual
  norm↓
    : {Y Z : Set}
    → {U : _}
    → {m : 𝔈 Nat Y Z}
    → U ⊩ m norm
    → 𝔅 Y Z
  norm↓ (norm-η x) =
    η x

  norm↓ (norm-ϝ p) =
    norm↓-ϝ p

  norm↓-ϝ
    : {Y Z : Set}
    → {U V : _}
    → {m : Y → 𝔈 Nat Y Z}
    → {i : Nat}
    → U ⊩?⟨ i ⟩ m norm⊣ V
    → 𝔅 Y Z

  norm↓-ϝ (norm-ϝ-cons-ze p) =
    norm↓ p

  norm↓-ϝ (norm-ϝ-cons-su p) =
    norm↓-ϝ p

  norm↓-ϝ (norm-ϝ-nil-ze p) =
    ϝ (norm↓ ∘ p)

  norm↓-ϝ (norm-ϝ-nil-su p) =
    ϝ (norm↓-ϝ ∘ p)


-- Then, we show that the proof theory is complete: that for any Escardó dialogue,
-- we can show that it is normalizable.
mutual
  norm↑
    : {Y Z : Set}
    → (U : _)
    → (m : 𝔈 Nat Y Z)
    → U ⊩ m norm
  norm↑ U (η x) =
    norm-η x

  norm↑ U (?⟨ i ⟩ m) =
    norm-ϝ (norm↑-ϝ _ _ i m)

  norm↑-ϝ
    : {Y Z : Set}
    → (U V : _)
    → (i : Nat)
    → (m : Y → 𝔈 Nat Y Z)
    → U ⊩?⟨ i ⟩ m norm⊣ V

  norm↑-ϝ U [] zero m =
    norm-ϝ-nil-ze λ x →
      norm↑ (U ⌢ x) (m x)

  norm↑-ϝ U [] (suc i) m =
    norm-ϝ-nil-su λ x →
      norm↑-ϝ (U ⌢ x) [] i m

  norm↑-ϝ U (x ∷ V) zero m =
    norm-ϝ-cons-ze (norm↑ U (m x))

  norm↑-ϝ U (x ∷ V) (suc i) m =
    norm-ϝ-cons-su (norm↑-ϝ U V i m)

norm↑₀ : {Y Z : Set} (m : 𝔈 Nat Y Z) → [] ⊩ m norm
norm↑₀ = norm↑ []

norm
  : {Y Z : Set}
  → 𝔈 Nat Y Z
  → 𝔅 Y Z
norm =
  norm↓
    ∘ norm↑₀

module ⊢ where
  import Spread.Core as 𝔖

  private
    _<++_ : {Y : Set} → List Y → 𝔖.Point Y → 𝔖.Point Y
    [] <++ α = α
    ((x ∷ xs) <++ α) zero = x
    ((x ∷ xs) <++ α) (suc i) = (xs <++ α) i

    prepend-snoc-id
      : {Y : Set}
      → (U : List Y)
      → (α : 𝔖.Point Y)
      → ∀ i → (U <++ α) i ≡ ((U ⌢ α 0) <++ (α ∘ suc)) i
    prepend-snoc-id [] α zero = refl
    prepend-snoc-id [] α (suc i) = refl
    prepend-snoc-id (x ∷ U) α zero = refl
    prepend-snoc-id (x ∷ U) α (suc i) = prepend-snoc-id U α i

  module Coh where
    mutual
      coh
        : {Y Z : Set}
        → {U : _}
        → (m : 𝔈 Nat Y Z)
        → (p : U ⊩ m norm)
        → (α : 𝔖.Point Y)
        → 𝔈[ m ⋄ (U <++ α) ] ≡ 𝔅[ norm↓ p ⋄ α ]
      coh .(η x) (norm-η x) α = refl
      coh _ (norm-ϝ p) = coh-ϝ _ _ _ _ p

      coh-ϝ
        : {Y Z : Set}
        → (U : _) (V : _)
        → (i : Nat)
        → (m : Y → 𝔈 Nat Y Z)
        → (p : U ⊩?⟨ i ⟩ m norm⊣ V)
        → (α : 𝔖.Point Y)
        → 𝔈[ m ((V <++ α) i) ⋄ (U <++ α) ] ≡ 𝔅[ norm↓-ϝ p ⋄ α ]

      coh-ϝ U (x ∷ V) .0 m (norm-ϝ-cons-ze p) α =
        coh (m x) p α

      coh-ϝ U (x ∷ V) (suc i) m (norm-ϝ-cons-su p) α =
        coh-ϝ U V i m p α

      coh-ϝ U .[] .0 m (norm-ϝ-nil-ze p) α =
        coh (m _) (p _) (α ∘ suc)
          ≡.▪ Core.⊢.⋄-extensional (m _) (prepend-snoc-id U α)

      coh-ϝ U .[] (suc i) m (norm-ϝ-nil-su p) α =
        coh-ϝ _ _ i m (p _) (α ∘ suc)
          ≡.▪ Core.⊢.⋄-extensional (m _) (prepend-snoc-id U α)


  coh
    : {Y Z : Set}
    → (m : 𝔈 Nat Y Z)
    → (α : 𝔖.Point Y)
    → 𝔈[ m ⋄ α ] ≡ 𝔅[ norm m ⋄ α ]
  coh m =
    Coh.coh m
      (norm↑ [] m)
