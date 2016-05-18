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


mutual
  data _⊩_norm {Y Z : Set} (U : List Y) : 𝓓 Y Z → Set where
    norm-η
      : ∀ x
      → U ⊩ η x norm

    norm-ϝ
      : ∀ {i 𝓭[_]}
      → U ⊩β⟨ i ⟩ 𝓭[_] norm⊣ U
      → U ⊩ β⟨ i ⟩ 𝓭[_] norm

  data _⊩β⟨_⟩_norm⊣_ {Y Z : Set} (U : List Y) : Nat → (Y → 𝓓 Y Z) → List Y → Set where
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


mutual
  run-norm : {Y Z : Set} {𝓭 : 𝓓 Y Z} {U : _} → U ⊩ 𝓭 norm → 𝓓ₙ Y Z
  run-norm (norm-η x) = η x
  run-norm (norm-ϝ p) = run-norm-ϝ p

  run-norm-ϝ : {Y Z : Set} {i : Nat} {𝓭[_] : Y → 𝓓 Y Z} {U V : _} → U ⊩β⟨ i ⟩ 𝓭[_] norm⊣ V → 𝓓ₙ Y Z
  run-norm-ϝ (norm-ϝ-cons-ze p) = run-norm p
  run-norm-ϝ (norm-ϝ-cons-su p) = run-norm-ϝ p
  run-norm-ϝ (norm-ϝ-nil-ze p[_]) = ϝ λ x → run-norm p[ x ]
  run-norm-ϝ (norm-ϝ-nil-su p[_]) = ϝ λ x → run-norm-ϝ p[ x ]

mutual
  compute-norm : {Y Z : Set} (U : _) (𝓭 : 𝓓 Y Z) → U ⊩ 𝓭 norm
  compute-norm U (η x) = norm-η x
  compute-norm U (β⟨ i ⟩ 𝓭[_]) = norm-ϝ (compute-norm-ϝ _ _ i 𝓭[_])

  compute-norm-ϝ : {Y Z : Set} (U V : _) (i : Nat) (𝓭[_] : Y → 𝓓 Y Z) → U ⊩β⟨ i ⟩ 𝓭[_] norm⊣ V
  compute-norm-ϝ U [] ze 𝓭[_] = norm-ϝ-nil-ze λ x → compute-norm (U ⌢ x) 𝓭[ x ]
  compute-norm-ϝ U [] (su_ i) 𝓭[_] = norm-ϝ-nil-su λ x → compute-norm-ϝ (U ⌢ x) [] i 𝓭[_]
  compute-norm-ϝ U (x ∷ V) ze 𝓭[_] = norm-ϝ-cons-ze (compute-norm U 𝓭[ x ])
  compute-norm-ϝ U (x ∷ V) (su_ i) 𝓭[_] = norm-ϝ-cons-su (compute-norm-ϝ U V i 𝓭[_])

compute-norm₀ : {Y Z : Set} (𝓭 : 𝓓 Y Z) → [] ⊩ 𝓭 norm
compute-norm₀ = compute-norm []

norm : {Y Z : Set} → 𝓓 Y Z → 𝓓ₙ Y Z
norm 𝓭 = run-norm (compute-norm₀ 𝓭)

module ⊢ where
  private
    prepend : {Y : Set} → List Y → Y ^ω → Y ^ω
    prepend [] α = α
    prepend (x ∷ xs) α ze = x
    prepend (x ∷ xs) α (su_ i) = prepend xs α i

    _⊕<_ : {Y : Set} → List Y → Y ^ω → Y ^ω
    _⊕<_ = prepend

    {-# DISPLAY prepend U α = U ⊕< α #-}

    prepend-snoc-id
      : {Y : Set}
      → (U : List Y)
      → (α : Y ^ω)
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
        → (𝓭 : 𝓓 Y Z)
        → (p : U ⊩ 𝓭 norm)
        → (α : Y ^ω)
        → 𝓭 $ (U ⊕< α) ≡ run-norm p $ₙ α
      coh .(η x) (norm-η x) α = refl
      coh _ (norm-ϝ {i = i} {𝓭[_] = 𝓭[_]} p) α =
        coh-ϝ _ i 𝓭[_] p α

      coh-ϝ
        : {Y Z : Set}
        → {U : _} (V : _)
        → (i : Nat)
        → (𝓭[_] : Y → 𝓓 Y Z)
        → (p : U ⊩β⟨ i ⟩ 𝓭[_] norm⊣ V)
        → (α : Y ^ω)
        → 𝓭[ (V ⊕< α) i ] $ (U ⊕< α) ≡ run-norm-ϝ p $ₙ α

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
    → (𝓭 : 𝓓 Y Z)
    → (α : Y ^ω)
    → 𝓭 $ α ≡ norm 𝓭 $ₙ α
  coh 𝓭 =
    Coh.coh 𝓭
      (compute-norm [] 𝓭)
