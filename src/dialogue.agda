module Dialogue where

open import Prelude.Functor
open import Prelude.Monad
open import Prelude.Monoidal
open import Prelude.Natural
open import Prelude.Path
open import Prelude.List

open Π using (_∘_)

Seq : Set → Set
Seq X = Nat → X

_^ω : Set → Set
X ^ω = Seq X

{-# DISPLAY Seq X = X ^ω #-}

-- A dialogue tree is precisely Brouwer's notion of a "mental construction"
-- of a functional on the points of a spread.
data 𝓓 (Y Z : Set) : Set where
  η_ : Z → 𝓓 Y Z
  ϝ : Nat → (Y → 𝓓 Y Z) → 𝓓 Y Z

-- In the normalized (Brouwerian) version of the dialogue tree, queries are given in order.
data 𝓓ₙ (Y Z : Set) : Set where
  η_ : Z → 𝓓ₙ Y Z
  ϝ : (Y → 𝓓ₙ Y Z) → 𝓓ₙ Y Z

snoc : {Y : Set} → List Y → Y → List Y
snoc [] x = x ∷ []
snoc (x ∷ xs) y = x ∷ (snoc xs y)

mutual
  data _⊩_norm {Y Z : Set} (U : List Y) : 𝓓 Y Z → Set where
    norm-η
      : ∀ x
      → U ⊩ η x norm

    norm-ϝ
      : ∀ {i 𝓭[_]}
      → U ⊩ϝ⟨ i ⟩ 𝓭[_] norm⊣ U
      → U ⊩ ϝ i 𝓭[_] norm

  data _⊩ϝ⟨_⟩_norm⊣_ {Y Z : Set} (U : List Y) : Nat → (Y → 𝓓 Y Z) → List Y → Set where
    norm-ϝ-cons-ze
      : ∀ {V x 𝓭[_]}
      → U ⊩ 𝓭[ x ] norm
      → U ⊩ϝ⟨ 0 ⟩ 𝓭[_] norm⊣ (x ∷ V)

    norm-ϝ-cons-su
      : ∀ {V x i 𝓭[_]}
      → U ⊩ϝ⟨ i ⟩ 𝓭[_] norm⊣ V
      → U ⊩ϝ⟨ su i ⟩ 𝓭[_] norm⊣ (x ∷ V)

    norm-ϝ-nil-ze
      : ∀ {𝓭[_]}
      → (∀ x → snoc U x ⊩ 𝓭[ x ] norm)
      → U ⊩ϝ⟨ 0 ⟩ 𝓭[_] norm⊣ []

    -- not sure if this is right
    norm-ϝ-nil-su
      : ∀ {i 𝓭[_]}
      → (∀ x → (snoc U x) ⊩ϝ⟨ i ⟩ 𝓭[_] norm⊣ [])
      → U ⊩ϝ⟨ su i ⟩ 𝓭[_] norm⊣ []

mutual
  run-norm : {Y Z : Set} {𝓭 : 𝓓 Y Z} {U : _} → U ⊩ 𝓭 norm → 𝓓ₙ Y Z
  run-norm (norm-η x) = η x
  run-norm (norm-ϝ p) = run-norm-ϝ p

  run-norm-ϝ : {Y Z : Set} {i : Nat} {𝓭[_] : Y → 𝓓 Y Z} {U V : _} → U ⊩ϝ⟨ i ⟩ 𝓭[_] norm⊣ V → 𝓓ₙ Y Z
  run-norm-ϝ (norm-ϝ-cons-ze p) = run-norm p
  run-norm-ϝ (norm-ϝ-cons-su p) = run-norm-ϝ p
  run-norm-ϝ (norm-ϝ-nil-ze p[_]) = ϝ λ x → run-norm p[ x ]
  run-norm-ϝ (norm-ϝ-nil-su p[_]) = ϝ λ x → run-norm-ϝ p[ x ]

mutual
  compute-norm : {Y Z : Set} (U : _) (𝓭 : 𝓓 Y Z) → U ⊩ 𝓭 norm
  compute-norm U (η x) = norm-η x
  compute-norm U (ϝ i 𝓭[_]) = norm-ϝ (compute-norm-ϝ _ _ i 𝓭[_])

  compute-norm-ϝ : {Y Z : Set} (U V : _) (i : Nat) (𝓭[_] : Y → 𝓓 Y Z) → U ⊩ϝ⟨ i ⟩ 𝓭[_] norm⊣ V
  compute-norm-ϝ U [] ze 𝓭[_] = norm-ϝ-nil-ze (λ x → compute-norm (snoc U x) 𝓭[ x ])
  compute-norm-ϝ U [] (su_ i) 𝓭[_] = norm-ϝ-nil-su (λ x → compute-norm-ϝ (snoc U x) [] i 𝓭[_]) -- (compute-norm-ϝ U [] i 𝓭[_])
  compute-norm-ϝ U (x ∷ V) ze 𝓭[_] = norm-ϝ-cons-ze (compute-norm U 𝓭[ x ])
  compute-norm-ϝ U (x ∷ V) (su_ i) 𝓭[_] = norm-ϝ-cons-su (compute-norm-ϝ U V i 𝓭[_])

norm : {Y Z : Set} → 𝓓 Y Z → 𝓓ₙ Y Z
norm 𝓭 = run-norm (compute-norm [] 𝓭)


eval : {Y Z : Set} → 𝓓 Y Z → Y ^ω → Z
eval (η x) α = x
eval (ϝ i 𝓭[_]) α = eval 𝓭[ α i ] α

evalₙ : {Y Z : Set} → 𝓓ₙ Y Z → Y ^ω → Z
evalₙ (η x) α = x
evalₙ (ϝ 𝓭[_]) α = evalₙ 𝓭[ α 0 ] (α ∘ su_)

⟦_⟧ : {Y Z : Set} → 𝓓 Y Z → Y ^ω → Z
⟦ 𝓭 ⟧ = eval 𝓭

⟦_⟧ₙ : {Y Z : Set} → 𝓓ₙ Y Z → Y ^ω → Z
⟦ 𝓭 ⟧ₙ = evalₙ 𝓭

{-# DISPLAY eval 𝓭 U α = ⟦ 𝓭 ⟧ α #-}
{-# DISPLAY evalₙ 𝓭 U α = ⟦ 𝓭 ⟧ₙ α #-}

module Tests where

  id : Nat ^ω
  id x = x

  test : 𝓓 Nat Nat
  test = ϝ 4 λ x → ϝ 5 λ y → η (x Nat.+ y)

  test2 : 𝓓ₙ Nat Nat
  test2 = norm test


  test-eq : ⟦ test ⟧ id ≡ ⟦ norm test ⟧ₙ id
  test-eq = refl

postulate
  coherence : {Y Z : Set} (𝓭 : 𝓓 Y Z) (α : Y ^ω) → ⟦ 𝓭 ⟧ α ≡ ⟦ norm 𝓭 ⟧ₙ α

-- A mental construction of a functional on the Baire space
𝓑 : Set → Set
𝓑 = 𝓓 Nat

𝓑ₙ : Set → Set
𝓑ₙ = 𝓓ₙ Nat

instance
  𝓓-functor : Functor 𝓑
  Functor.map 𝓓-functor f (η x) = η (f x)
  Functor.map 𝓓-functor f (ϝ i 𝓭[_]) = ϝ i λ x → map f 𝓭[ x ]

  𝓓-monad : Monad 𝓑
  Monad.return_ 𝓓-monad = η_
  Monad.bind 𝓓-monad κ (η x) = κ x
  Monad.bind 𝓓-monad κ (ϝ i 𝓭[_]) = ϝ i λ x → Monad.bind 𝓓-monad κ 𝓭[ x ]

{-# DISPLAY 𝓓-functor f 𝓭 = map f 𝓭 #-}
{-# DISPLAY 𝓓-monad κ 𝓭 = 𝓭 ≫= κ #-}

module ⊢ where

  eval-natural
    : {X Y : Set}
    → (f : X → Y)
    → (𝓭 : 𝓑 X)
    → (α : Nat ^ω)
    → f (⟦ 𝓭 ⟧ α) ≡ ⟦ map f 𝓭 ⟧ α
  eval-natural f (η x) α =
    refl
  eval-natural f (ϝ i 𝓭[_]) α =
    eval-natural f 𝓭[ α i ] α

{-
  -- uh-oh! Is this even true?
  eval-bind-law
    : {X Y : Set}
    → (𝓯[_] : X → 𝓑 Y)
    → (𝓭 : 𝓑 X)
    → (α : Nat ^ω)
    → ⟦ 𝓯[ ⟦ 𝓭 ⟧ α ] ⟧ α ≡ ⟦ 𝓭 ≫= 𝓯[_] ⟧ α
  eval-bind-law 𝓯[_] (η x) α = refl
  eval-bind-law 𝓯[_] (ϝ 𝓭[_]) α = {!!}
-}
