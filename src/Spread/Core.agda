module Spread.Core (X : Set) where

open import Prelude.Natural
open import Prelude.Path
open import Prelude.Monoidal

open Π using (_∘_)

module Neigh where
  data Neigh : Set where
    [] : Neigh
    _⌢_ : Neigh → X → Neigh

  infixl 5 _⌢_

  len : Neigh → Nat
  len [] = 0
  len (U ⌢ x) = su (len U)

  ∣_∣ : Neigh → Nat
  ∣_∣ = len

  {-# DISPLAY len U = ∣ U ∣ #-}

  module ⊢ where
    _⟨⌢⟩_ : ∀ {U V : Neigh} {x y} → U ≡ V → x ≡ y → U ⌢ x ≡ V ⌢ y
    refl ⟨⌢⟩ refl = refl

module Point where

  Point : Set
  Point = Nat → X

  head : Point → X
  head α = α 0

  tail : Point → Point
  tail α = α ∘ su_

  cons : X → Point → Point
  cons x α ze = x
  cons x α (su i) = α i

  _∷_ : X → Point → Point
  _∷_ = cons

  {-# DISPLAY cons x α = x ∷ α #-}

  _≈_ : Point → Point → Set
  α ≈ β = (i : Nat) → α i ≡ β i

  open Neigh hiding (module ⊢)

  prepend
    : Neigh
    → Point
    → Point
  prepend [] α i =
    α i
  prepend (U ⌢ x) α =
    prepend U (cons x α)

  _⊕<_
    : Neigh
    → Point
    → Point
  _⊕<_ =
    prepend

  infixr 4 _⊕<_

  {-# DISPLAY prepend U α = U ⊕< α #-}

  take
    : Nat
    → Point
    → Neigh
  take ze α = []
  take (su n) α = (take n α) ⌢ (α n)

  _[_]
    : Point
    → Nat
    → Neigh
  α [ n ] = take n α

  {-# DISPLAY take n α = α [ n ] #-}

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
      → take m α ≡ take n β
    take-cong {m = ze} {n = .0} refl q = refl
    take-cong {m = (su m)} {n = .(su m)} refl q
      rewrite take-cong {m = m} refl q
        | q m
        = refl

    open Nat using (_+_)

    su-+-transpose
      : ∀ m n
      → su (n + m) ≡ n + su m
    su-+-transpose ze ze = refl
    su-+-transpose ze (su_ n)
      rewrite su-+-transpose ze n
        = refl
    su-+-transpose (su m) ze = refl
    su-+-transpose (su m) (su_ n)
      rewrite su-+-transpose (su m) n
        = refl

    prepend-len
      : ∀ U n {α}
      → (U ⊕< α) (n + ∣ U ∣) ≡ α n
    prepend-len [] n
      rewrite Nat.⊢.ρ⇒ {n}
        = refl
    prepend-len (U ⌢ x) n =
      prepend-len U (su n) ≡.⟔
        nth-cong
          (U ⌢ x ⊕< _)
          _
          (λ i → refl)
          (su-+-transpose ∣ U ∣ n ≡.⁻¹)

    prepend-take-len
      : ∀ U {α}
      → take ∣ U ∣ (U ⊕< α) ≡ U
    prepend-take-len [] = refl
    prepend-take-len (U ⌢ x) =
      prepend-take-len U
        Neigh.⊢.⟨⌢⟩ prepend-len U 0

module Species where
  open Neigh

  Species : Set₁
  Species =
    Neigh
      → Set

  monotone
    : Species
    → Set
  monotone 𝔄 =
    {U : Neigh} {x : X}
      → 𝔄 U
      → 𝔄 (U ⌢ x)

  hereditary
    : Species
    → Set
  hereditary 𝔄 =
    {U : Neigh}
      → (∀ x → 𝔄 (U ⌢ x))
      → 𝔄 U

  _⊑_ : Species → Species → Set
  𝔄 ⊑ 𝔅 = ∀ x → 𝔄 x → 𝔅 x

open Point public hiding (module ⊢)
open Neigh public hiding (module Neigh; module ⊢)
open Species public
