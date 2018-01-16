module SystemT.Context where

open import Basis

data _^_ (X : Set) : Nat → Set where
  ⋄ : X ^ 0
  _,_ : {n : Nat} → X ^ n → X → X ^ (suc n)

_[_] : {X : Set} {n : Nat} → X ^ n → Fin n → X
(Γ , x) [ zero ] = x
(Γ , x) [ suc i ] = Γ [ i ]

infixl 3 _,_

record Ren {A : Set} {m n} (Γ : A ^ m) (Δ : A ^ n) : Set where
  field
    ap : Fin m → Fin n
    coh : ∀ i → Γ [ i ] ≡ Δ [ ap i ]

ren-extend : ∀ {A : Set} {m n σ} {Γ : A ^ m} {Δ : A ^ n} → Ren Γ Δ → Ren (Γ , σ) (Δ , σ)
Ren.ap (ren-extend ρ) zero = zero
Ren.ap (ren-extend ρ) (suc i) = suc (Ren.ap ρ i)
Ren.coh (ren-extend ρ) zero = refl
Ren.coh (ren-extend ρ) (suc i) rewrite Ren.coh ρ i = refl
