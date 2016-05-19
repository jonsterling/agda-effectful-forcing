module SystemT.Context where

open import Prelude.Natural
open import Prelude.Finite
open import Prelude.Path

data _^_ (X : Set) : Nat → Set where
  ⋄ : X ^ 0
  _,_ : {n : Nat} → X ^ n → X → X ^ (su n)

_[_] : {X : Set} {n : Nat} → X ^ n → Fin n → X
(Γ , x) [ ze ] = x
(Γ , x) [ su i ] = Γ [ i ]

infixl 3 _,_

record Ren {A : Set} {m n} (Γ : A ^ m) (Δ : A ^ n) : Set where
  field
    ap : Fin m → Fin n
    coh : ∀ i → Γ [ i ] ≡ Δ [ ap i ]

ren-extend : ∀ {A : Set} {m n σ} {Γ : A ^ m} {Δ : A ^ n} → Ren Γ Δ → Ren (Γ , σ) (Δ , σ)
Ren.ap (ren-extend ρ) ze = ze
Ren.ap (ren-extend ρ) (su i) = su (Ren.ap ρ i)
Ren.coh (ren-extend ρ) ze = refl
Ren.coh (ren-extend ρ) (su i) rewrite Ren.coh ρ i = refl
