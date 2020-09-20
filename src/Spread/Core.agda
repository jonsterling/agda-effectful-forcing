{-# OPTIONS --without-K #-}

module Spread.Core (X : Set) where

open import Basis

module Node where
  data Node : Set where
    [] : Node
    _⌢_ : Node → X → Node

  infixl 5 _⌢_

  ∣_∣ : Node → Nat
  ∣ [] ∣ = 0
  ∣ U ⌢ x ∣ = suc ∣ U ∣

  module ⊢ where
    _⟨⌢⟩_ : ∀ {U V : Node} {x y} → U ≡ V → x ≡ y → U ⌢ x ≡ V ⌢ y
    refl ⟨⌢⟩ refl = refl

module Point where

  Point : Set
  Point = Nat → X

  head : Point → X
  head α = α 0

  tail : Point → Point
  tail α = α ∘ suc

  _<∷_ : X → Point → Point
  (x <∷ α) zero = x
  (x <∷ α) (suc i) = α i

  _≈_ : Point → Point → Set
  α ≈ β = (i : Nat) → α i ≡ β i

  open Node hiding (module ⊢)

  _<++_ : Node → Point → Point
  [] <++ α = α
  (U ⌢ x) <++ α = U <++ (x <∷ α)

  infixr 3 _<++_
  infix 2 _[_]
  infix 1 _≈_

  _[_]
    : Point
    → Nat
    → Node
  α [ zero ] = []
  α [ suc n ] = (α [ n ]) ⌢ α n

  module ⊢ where
    nth-cong
      : (α β : Point) {i j : Nat}
      → α ≈ β
      → i ≡ j
      → α i ≡ β j
    nth-cong α β h refl =
      h _

    take-cong
      : ∀ {α β m n}
      → m ≡ n
      → α ≈ β
      → (α [ m ]) ≡ (β [ n ])
    take-cong {m = zero} {n = .0} refl q = refl
    take-cong {m = (suc m)} {n = .(suc m)} refl q
      rewrite take-cong {m = m} refl q
        | q m
        = refl

    su-+-transpose
      : ∀ m n
      → suc (n + m) ≡ n + suc m
    su-+-transpose zero zero = refl
    su-+-transpose zero (suc n)
      rewrite su-+-transpose zero n
        = refl
    su-+-transpose (suc m) zero = refl
    su-+-transpose (suc m) (suc n)
      rewrite su-+-transpose (suc m) n
        = refl

    nat-+-zero
      : ∀ n
      → n + 0 ≡ n
    nat-+-zero zero = refl
    nat-+-zero (suc n) rewrite nat-+-zero n = refl

    prepend-len
      : ∀ U n {α}
      → (U <++ α) (n + ∣ U ∣) ≡ α n
    prepend-len [] n rewrite nat-+-zero n = refl
    prepend-len (U ⌢ x) n =
      prepend-len U (suc n)
      ≡.▪
        nth-cong
          (U ⌢ x <++ _)
          _
          (λ i → refl)
          (su-+-transpose ∣ U ∣ n ≡.⁻¹)


    prepend-take-len
      : ∀ U {α}
      → ((U <++ α) [ ∣ U ∣ ]) ≡ U
    prepend-take-len [] = refl
    prepend-take-len (U ⌢ x) =
      prepend-take-len U
        Node.⊢.⟨⌢⟩ prepend-len U 0

    cons-head-tail-id
      : ∀ α
      → α ≈ (head α <∷ tail α)
    cons-head-tail-id α zero = refl
    cons-head-tail-id α (suc i) = refl

    prepend-extensional
      : ∀ U α β
      → α ≈ β
      → U <++ α ≈ U <++ β
    prepend-extensional [] α β h = h
    prepend-extensional (U ⌢ x) α β h =
      prepend-extensional U (x <∷ α) (x <∷ β) λ
        { zero → refl
        ; (suc j) → h j
        }

    prepend-snoc-id
      : ∀ U α
      → (U <++ α) ≈ (U ⌢ head α <++ tail α)
    prepend-snoc-id U α =
      prepend-extensional U _ _ (cons-head-tail-id α)

module Species where
  open Node

  Species : Set₁
  Species =
    Node
      → Set

  monotone
    : Species
    → Set
  monotone 𝔄 =
    {U : Node} {x : X}
      → 𝔄 U
      → 𝔄 (U ⌢ x)

  hereditary
    : Species
    → Set
  hereditary 𝔄 =
    {U : Node}
      → (∀ x → 𝔄 (U ⌢ x))
      → 𝔄 U

  _⊑_ : Species → Species → Set
  𝔄 ⊑ 𝔅 = ∀ x → 𝔄 x → 𝔅 x

open Point public hiding (module ⊢)
open Node public hiding (module Node; module ⊢)
open Species public
