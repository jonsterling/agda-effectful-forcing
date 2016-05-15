module Baire where

open import Prelude.Monoidal
open import Prelude.Natural
open import Prelude.Path

open import Prelude.Functor
open import Prelude.Monad

open import Dialogue

open Π using (_∘_)

-- The Baire Space is Brouwer's universal spread.

-- A mental construction of a functional on the Baire space
𝓑 : Set → Set
𝓑 = 𝓓 Nat

instance
  𝔅-Functor : Functor 𝓑
  Functor.map 𝔅-Functor f (η n) = η (f n)
  Functor.map 𝔅-Functor f (ϝ 𝓭[_]) = ϝ λ x → map f 𝓭[ x ]

  𝓑-Monad : Monad 𝓑
  Monad.return_ 𝓑-Monad = η
  Monad.bind 𝓑-Monad κ (η n) = κ n
  Monad.bind 𝓑-Monad κ (ϝ 𝓭[_]) = ϝ λ x → Monad.bind 𝓑-Monad κ 𝓭[ x ]

module Neigh where
  data Neigh : Set where
    [] : Neigh
    _⌢_ : Neigh → Nat → Neigh

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
  -- A point in the Baire spread is a sequence of natural numbers.
  Point : Set
  Point = Seq Nat

  head : Point → Nat
  head α = α 0

  tail : Point → Point
  tail α = α ∘ su_

  cons : Nat → Point → Point
  cons x α ze = x
  cons x α (su i) = α i

  _∷_ : Nat → Point → Point
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
  monotone φ =
    {U : Neigh} {x : Nat}
      → φ U
      → φ (U ⌢ x)

open Point public hiding (module ⊢)
open Neigh public hiding (module Neigh; module ⊢)
open Species public
