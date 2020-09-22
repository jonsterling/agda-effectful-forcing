{-# OPTIONS --without-K #-}

open import Basis

module Algebra (T : Set → Set) ⦃ T-monad : Monad T ⦄ where

record Alg : Set₁ where
  constructor algebra
  field
    car : Set
    alg : T car → car
    law/η : ∀ x → alg (ret x) ≡ x
    law/μ : ∀ (m : T (T car)) → alg (map alg m) ≡ alg (join m)

F : Set → Alg
Alg.car (F A) = T A
Alg.alg (F A) = join
Alg.law/η (F A) _ = law/λ
Alg.law/μ (F A) m =
  ≡.seq
   (law/α m)
   (≡.seq
    (≡.cong (m >>=_) (funext λ _ → law/λ))
    (≡.inv (law/α m)))

U : Alg → Set
U = Alg.car

Alg/Π : (A : Set) → (A → Alg) → Alg

Alg.car (Alg/Π A B) =
  (x : A) → Alg.car (B x)

Alg.alg (Alg/Π A B) m x =
  Alg.alg (B x) (map (λ f → f x) m)

Alg.law/η (Alg/Π A B) f =
  depfunext λ x →
  ≡.seq
   (≡.cong (Alg.alg (B x)) law/λ)
   (Alg.law/η (B x) (f x))

Alg.law/μ (Alg/Π A B) m =
  depfunext λ x →
  ≡.seq
   (≡.cong
    (Alg.alg (B x))
    (≡.seq
     (law/α m)
     (≡.seq
      (≡.cong
       (m >>=_)
       (funext λ _ →
        ≡.seq law/λ (≡.inv law/λ)))
      (≡.inv
       (law/α m)))))
   (≡.seq
    (Alg.law/μ (B x) (map (map (λ f → f x)) m))
    (≡.cong
     (Alg.alg (B x))
     (≡.seq
      (law/α m)
      (≡.seq
       (≡.cong
        (m >>=_)
        (funext λ _ → law/λ))
       (≡.inv
        (law/α m))))))


Alg[_⇒_] : Set → Alg → Alg
Alg[ A ⇒ B ] = Alg/Π A λ _ → B
