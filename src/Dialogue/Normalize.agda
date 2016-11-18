module Dialogue.Normalize where

open import Prelude.List
open import Prelude.Natural
open import Prelude.Monoidal
open import Prelude.Path

import Dialogue.Core as Core
open Core hiding (module ⊢)

open import Dialogue.Brouwerian

open Π using (_∘_)

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
      : ∀ {i 𝓭[_]}
      → U ⊩β⟨ i ⟩ 𝓭[_] norm⊣ U
      → U ⊩ β⟨ i ⟩ 𝓭[_] norm

  data _⊩β⟨_⟩_norm⊣_ {Y Z : Set} (U : List Y) : Nat → (Y → 𝔈 Nat Y Z) → List Y → Set where
    norm-ϝ-cons-ze
      : ∀ {V x 𝓭[_]}
      → U ⊩ 𝓭[ x ] norm
      → U ⊩β⟨ 0 ⟩ 𝓭[_] norm⊣ (x ∷ V)

    norm-ϝ-cons-su
      : ∀ {V x i 𝓭[_]}
      → U ⊩β⟨ i ⟩ 𝓭[_] norm⊣ V
      → U ⊩β⟨ su i ⟩ 𝓭[_] norm⊣ (x ∷ V)

    norm-ϝ-nil-ze
      : ∀ {𝓭[_]}
      → (∀ x → (U ⌢ x) ⊩ 𝓭[ x ] norm)
      → U ⊩β⟨ 0 ⟩ 𝓭[_] norm⊣ []

    norm-ϝ-nil-su
      : ∀ {i 𝓭[_]}
      → (∀ x → (U ⌢ x) ⊩β⟨ i ⟩ 𝓭[_] norm⊣ [])
      → U ⊩β⟨ su i ⟩ 𝓭[_] norm⊣ []

-- Next, we show that the proof-theoretic characterization of
-- tree normalizability was sound, i.e. that whenever the judgment
-- holds for an Escardó dialogue, we can compute the corresponding
-- Brouwerian mental construction.
mutual
  norm↓
    : {Y Z : Set}
    → {U : _}
    → {𝓭 : 𝔈 Nat Y Z}
    → U ⊩ 𝓭 norm
    → 𝔅 Y Z
  norm↓ (norm-η x) =
    η x

  norm↓ (norm-ϝ p) =
    norm↓-ϝ p

  norm↓-ϝ
    : {Y Z : Set}
    → {U V : _}
    → {𝓭[_] : Y → 𝔈 Nat Y Z}
    → {i : Nat}
    → U ⊩β⟨ i ⟩ 𝓭[_] norm⊣ V
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
    → (𝓭 : 𝔈 Nat Y Z)
    → U ⊩ 𝓭 norm
  norm↑ U (η x) =
    norm-η x

  norm↑ U (β⟨ i ⟩ 𝓭[_]) =
    norm-ϝ (norm↑-ϝ _ _ i 𝓭[_])

  norm↑-ϝ
    : {Y Z : Set}
    → (U V : _)
    → (i : Nat)
    → (𝓭 : Y → 𝔈 Nat Y Z)
    → U ⊩β⟨ i ⟩ 𝓭 norm⊣ V

  norm↑-ϝ U [] ze 𝓭 =
    norm-ϝ-nil-ze λ x →
      norm↑ (U ⌢ x) (𝓭 x)

  norm↑-ϝ U [] (su_ i) 𝓭 =
    norm-ϝ-nil-su λ x →
      norm↑-ϝ (U ⌢ x) [] i 𝓭

  norm↑-ϝ U (x ∷ V) ze 𝓭 =
    norm-ϝ-cons-ze (norm↑ U (𝓭 x))

  norm↑-ϝ U (x ∷ V) (su_ i) 𝓭 =
    norm-ϝ-cons-su (norm↑-ϝ U V i 𝓭)

norm↑₀ : {Y Z : Set} (𝓭 : 𝔈 Nat Y Z) → [] ⊩ 𝓭 norm
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
    prepend : {Y : Set} → List Y → 𝔖.Point Y → 𝔖.Point Y
    prepend [] α = α
    prepend (x ∷ xs) α ze = x
    prepend (x ∷ xs) α (su_ i) = prepend xs α i

    _⊕<_ : {Y : Set} → List Y → 𝔖.Point Y → 𝔖.Point Y
    _⊕<_ = prepend

    {-# DISPLAY prepend U α = U ⊕< α #-}

    prepend-snoc-id
      : {Y : Set}
      → (U : List Y)
      → (α : 𝔖.Point Y)
      → ∀ i → (U ⊕< α) i ≡ ((U ⌢ α 0) ⊕< (α ∘ su_)) i
    prepend-snoc-id [] α ze = refl
    prepend-snoc-id [] α (su_ i) = refl
    prepend-snoc-id (x ∷ U) α ze = refl
    prepend-snoc-id (x ∷ U) α (su_ i) = prepend-snoc-id U α i

  module Coh where
    mutual
      coh
        : {Y Z : Set}
        → {U : _}
        → (𝓭 : 𝔈 Nat Y Z)
        → (p : U ⊩ 𝓭 norm)
        → (α : 𝔖.Point Y)
        → 𝓭 $ (U ⊕< α) ≡ norm↓ p $ₙ α
      coh .(η x) (norm-η x) α = refl
      coh _ (norm-ϝ {i = i} {𝓭[_] = 𝓭[_]} p) α =
        coh-ϝ _ i 𝓭[_] p α

      coh-ϝ
        : {Y Z : Set}
        → {U : _} (V : _)
        → (i : Nat)
        → (𝓭[_] : Y → 𝔈 Nat Y Z)
        → (p : U ⊩β⟨ i ⟩ 𝓭[_] norm⊣ V)
        → (α : 𝔖.Point Y)
        → 𝓭[ (V ⊕< α) i ] $ (U ⊕< α) ≡ norm↓-ϝ p $ₙ α

      coh-ϝ {U = U} (x ∷ V) .0 𝓭[_] (norm-ϝ-cons-ze p) α =
        coh {U = U} 𝓭[ x ] p α

      coh-ϝ (x ∷ V) (su i) 𝓭[_] (norm-ϝ-cons-su p) α =
        coh-ϝ V i 𝓭[_] p α

      coh-ϝ {U = U} .[] .0 𝓭[_] (norm-ϝ-nil-ze p[_]) α =
        coh 𝓭[ α 0 ] p[ α 0 ] (α ∘ su_)
          ≡.⟔ 𝓭[ α 0 ] Core.⊢.$¹ (prepend-snoc-id U α)

      coh-ϝ {U = U} .[] (su i) 𝓭[_] (norm-ϝ-nil-su p[_]) α =
        coh-ϝ _ i 𝓭[_] p[ α 0 ] (α ∘ su_)
          ≡.⟔ 𝓭[ α (su i) ] Core.⊢.$¹ (prepend-snoc-id U α)


  coh
    : {Y Z : Set}
    → (𝓭 : 𝔈 Nat Y Z)
    → (α : 𝔖.Point Y)
    → 𝓭 $ α ≡ norm 𝓭 $ₙ α
  coh 𝓭 =
    Coh.coh 𝓭
      (norm↑ [] 𝓭)
