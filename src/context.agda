module Context where

open import Prelude.Natural
open import Prelude.Finite

data _^_ (X : Set) : Nat → Set where
  ⋄ : X ^ 0
  _,_ : {n : Nat} → X ^ n → X → X ^ (su n)

_[_] : {X : Set} {n : Nat} → X ^ n → Fin n → X
(Γ , x) [ ze ] = x
(Γ , x) [ su i ] = Γ [ i ]
