{-# OPTIONS --without-K #-}

module SystemT.Semantics where

open import Basis
open import SystemT.Context
open import SystemT.Syntax
import Dialogue as 𝓓
import Spread.Baire

rec : {X : Set} → (ℕ → X → X) → X → ℕ → X
rec f x zero = x
rec f x (suc n) = f n (rec f x n)

module StandardSemantics where
  ⟦_⟧ : Type → Set
  ⟦ nat ⟧ = ℕ
  ⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

  cx⟦_⟧ : {n : ℕ} → Ctx n → Set
  cx⟦ Γ ⟧ = (i : Fin _) → ⟦ Γ [ i ] ⟧

  ⟦⋄⟧ : cx⟦ ⋄ ⟧
  ⟦⋄⟧ ()

  _⟦,⟧_ : ∀ {n} {Γ : Ctx n} {σ : Type} → cx⟦ Γ ⟧ → ⟦ σ ⟧ → cx⟦ Γ , σ ⟧
  (ρ ⟦,⟧ x) zero = x
  (ρ ⟦,⟧ x) (suc i) = ρ i

  infixl 5 _⟦,⟧_

  tm⟦_⟧
    : ∀ {n τ} {Γ : Ctx n}
    → Γ ⊢ᵀ τ
    → cx⟦ Γ ⟧
    → ⟦ τ ⟧

  tm⟦ zero ⟧ _ = zero
  tm⟦ succ m ⟧ ρ = suc (tm⟦ m ⟧ ρ)

  tm⟦ rec[ σ ] s z n ⟧ ρ =
   rec
    (λ x y → tm⟦ s ⟧ (ρ ⟦,⟧ x ⟦,⟧ y ))
    (tm⟦ z ⟧ ρ)
    (tm⟦ n ⟧ ρ)

  tm⟦ ν i q ⟧ ρ =
    ≡.use ρ i by
      ≡.cong ⟦_⟧ (≡.inv q)
    ∎

  tm⟦ ƛ t ⟧ ρ x = tm⟦ t ⟧ (ρ ⟦,⟧ x)
  tm⟦ m · n ⟧ ρ = tm⟦ m ⟧ ρ (tm⟦ n ⟧ ρ)

  tm⟦_⟧₀
    : ∀ {τ}
    → ⋄ ⊢ᵀ τ
    → ⟦ τ ⟧
  tm⟦ t ⟧₀ = tm⟦ t ⟧ ⟦⋄⟧

module AlgebraSemantics (T : Set → Set) ⦃ T-monad : Monad T ⦄ where
  open import Algebra T public
  ⟪_⟫ : Type → Alg
  ⟪ nat ⟫ = F ℕ
  ⟪ σ ⇒ τ ⟫ = Alg[ U ⟪ σ ⟫ ⇒ ⟪ τ ⟫ ]

  cx⟪_⟫ : {n : ℕ} → Ctx n → Alg
  cx⟪_⟫ {n} Γ = Alg/Π (Fin n) λ i → ⟪ Γ [ i ] ⟫

  _⟪,⟫_ : ∀ {n} {Γ : Ctx n} {σ : Type} → U cx⟪ Γ ⟫ → U ⟪ σ ⟫ → U cx⟪ Γ , σ ⟫
  (ρ ⟪,⟫ x) zero = x
  (ρ ⟪,⟫ x) (suc i) = ρ i

  infixl 5 _⟪,⟫_

  ⟪⋄⟫ : U cx⟪ ⋄ ⟫
  ⟪⋄⟫ ()

  tm⟪_⟫
    : ∀ {n τ} {Γ : Ctx n}
    → Γ ⊢ᵀ τ
    → U cx⟪ Γ ⟫
    → U ⟪ τ ⟫
  tm⟪ zero ⟫ ρ = ret zero
  tm⟪ succ x ⟫ ρ = map suc (tm⟪ x ⟫ ρ)
  tm⟪ rec[ σ ] s z n ⟫ ρ =
    Alg.alg ⟪ σ ⟫ do
      n ← tm⟪ n ⟫ ρ
      rec (λ x ih → ret (tm⟪ s ⟫ (ρ ⟪,⟫ ret x ⟪,⟫ Alg.alg ⟪ σ ⟫ ih))) (ret (tm⟪ z ⟫ ρ)) n

  tm⟪ ν i q ⟫ ρ =
    ≡.use ρ i by
      ≡.cong (U ∘ ⟪_⟫) (≡.inv q)
    ∎

  tm⟪ ƛ t ⟫ ρ x = tm⟪ t ⟫ (ρ ⟪,⟫ x)
  tm⟪ t · u ⟫ ρ = tm⟪ t ⟫ ρ (tm⟪ u ⟫ ρ)

  tm⟪_⟫₀
    : ∀ {τ}
    → ⋄ ⊢ᵀ τ
    → U ⟪ τ ⟫
  tm⟪ t ⟫₀ =
    tm⟪ t ⟫ ⟪⋄⟫


𝔈 = 𝓓.𝔈 ℕ ℕ
open AlgebraSemantics 𝔈 public
open StandardSemantics public

open Spread.Baire using (Point)
open 𝓓 using (𝔈[_⋄_]; ask)

module Coh where
  _⊨_∋_∼_
    : (α : Point)
    → (σ : Type)
    → (⟦s⟧ : ⟦ σ ⟧)
    → (⟪s⟫ : U ⟪ σ ⟫)
    → Set

  α ⊨ nat ∋ ⟦n⟧ ∼ ⟪n⟫ =
    ⟦n⟧ ≡ 𝔈[ ⟪n⟫ ⋄ α ]

  α ⊨ σ ⇒ τ ∋ ⟦f⟧ ∼ ⟪f⟫ =
    (⟦s⟧ : ⟦ σ ⟧)
    (⟪s⟫ : U ⟪ σ ⟫)
    → α ⊨ σ ∋ ⟦s⟧ ∼ ⟪s⟫
    → α ⊨ τ ∋ ⟦f⟧ ⟦s⟧ ∼ ⟪f⟫ ⟪s⟫

  _⊨cx_∋_∼_
    : {n : ℕ}
    → (α : Point)
    → (Γ : Ctx n)
    → (⟦ρ⟧ : cx⟦ Γ ⟧)
    → (⟪ρ⟫ : U cx⟪ Γ ⟫)
    → Set

  α ⊨cx Γ ∋ ⟦ρ⟧ ∼ ⟪ρ⟫ =
    (i : Fin _)
    → α ⊨ Γ [ i ] ∋ ⟦ρ⟧ i ∼ ⟪ρ⟫ i

  lift-sequence
    : (σ : Type)
    → (α : Point)
    → (⟦s⟧ : ℕ → ⟦ σ ⟧)
    → (⟪s⟫ : ℕ → U ⟪ σ ⟫)
    → ((k : ℕ) → α ⊨ σ ∋ ⟦s⟧ k ∼ ⟪s⟫ k)
    → (⟦n⟧ : ℕ)
    → (⟪n⟫ : 𝔈 ℕ)
    → α ⊨ nat ∋ ⟦n⟧ ∼ ⟪n⟫
    → α ⊨ σ ∋ ⟦s⟧ ⟦n⟧ ∼ Alg.alg ⟪ σ ⟫ (⟪n⟫ >>= (ret ∘ ⟪s⟫))

  lift-sequence nat α ⟦s⟧ ⟪s⟫ ⟦s⟧∼⟪s⟫ ⟦n⟧ ⟪n⟫ ⟦n⟧∼⟪n⟫ =
    ≡.seq
     (⟦s⟧∼⟪s⟫ ⟦n⟧)
     (≡.seq
      (≡.cong
       (𝔈[_⋄ α ] ∘ ⟪s⟫)
       ⟦n⟧∼⟪n⟫)
      (≡.seq
       (𝓓.⊢.⋄-commutes-with-bind ⟪n⟫ α)
       (≡.cong
        𝔈[_⋄ α ]
        (≡.inv
         (law/α ⟪n⟫)))))

  lift-sequence (σ ⇒ τ) α ⟦f⟧ ⟪f⟫ ⟦f⟧∼⟪f⟫ ⟦n⟧ ⟪n⟫ ⟦n⟧∼⟪n⟫ ⟦s⟧ ⟪s⟫ ⟦s⟧∼⟪s⟫ =
    let ih = lift-sequence _ _ _ _ (λ k → ⟦f⟧∼⟪f⟫ k ⟦s⟧ ⟪s⟫ ⟦s⟧∼⟪s⟫) ⟦n⟧ ⟪n⟫ ⟦n⟧∼⟪n⟫ in
    ≡.use ih by
      ≡.cong
       (α ⊨ τ ∋ ⟦f⟧ ⟦n⟧ ⟦s⟧ ∼_ ∘ Alg.alg ⟪ τ ⟫)
       (≡.inv
        (law/α ⟪n⟫))
    ∎


  -- Using our family of logical relations, we prove that the non-standard
  -- dialogue interpretation of System T coheres with the standard interpretation.
  hauptsatz
    : {n : ℕ}
    → {Γ : Ctx n}
    → {σ : Type}
    → (α : Point)
    → (s : Γ ⊢ᵀ σ)
    → (⟦ρ⟧ : cx⟦ Γ ⟧)
    → (⟪ρ⟫ : U cx⟪ Γ ⟫)
    → α ⊨cx Γ ∋ ⟦ρ⟧ ∼ ⟪ρ⟫
    → α ⊨ σ ∋ tm⟦ s ⟧ ⟦ρ⟧ ∼ tm⟪ s ⟫ ⟪ρ⟫

  hauptsatz α zero ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫ =
    refl

  hauptsatz α (succ n) ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫ =
    ≡.seq
     (≡.cong suc
      (hauptsatz _ n _ _ ⟦ρ⟧∼⟪ρ⟫))
     (𝓓.⊢.⋄-natural suc (tm⟪ n ⟫ ⟪ρ⟫) α)

  hauptsatz α (rec[ σ ] s z n) ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫ =
    let ih = lift-sequence _ _ ⟦rec⟧ ⟪rec⟫ ⟦rec⟧∼⟪rec⟫ ⟦n⟧ ⟪n⟫ ⟦n⟧∼⟪n⟫ in
    ≡.use ih by
      ≡.cong
       (α ⊨ σ ∋ ⟦rec⟧ ⟦n⟧ ∼_ ∘ Alg.alg ⟪ σ ⟫ ∘ (⟪n⟫ >>=_))
       (funext aux)
    ∎

    where
      ⟦n⟧ = tm⟦ n ⟧ ⟦ρ⟧
      ⟪n⟫ = tm⟪ n ⟫ ⟪ρ⟫
      ⟦n⟧∼⟪n⟫ = hauptsatz α n ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫

      ⟦z⟧ = tm⟦ z ⟧ ⟦ρ⟧
      ⟪z⟫ = tm⟪ z ⟫ ⟪ρ⟫
      ⟦z⟧∼⟪z⟫ = hauptsatz α z ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫

      ⟦s⟧ = λ x ih → tm⟦ s ⟧ (⟦ρ⟧ ⟦,⟧ x ⟦,⟧ ih)
      ⟪s⟫ = λ x ih → tm⟪ s ⟫ (⟪ρ⟫ ⟪,⟫ x ⟪,⟫ ih)

      ⟦s⟧∼⟪s⟫ =
        λ ⟦x⟧ ⟪x⟫ ⟦x⟧∼⟪x⟫ ⟦ih⟧ ⟪ih⟫ ⟦ih⟧∼⟪ih⟫ →
        hauptsatz α s (⟦ρ⟧ ⟦,⟧ ⟦x⟧ ⟦,⟧ ⟦ih⟧) (⟪ρ⟫ ⟪,⟫ ⟪x⟫ ⟪,⟫ ⟪ih⟫) λ where
          zero → ⟦ih⟧∼⟪ih⟫
          (suc zero) → ⟦x⟧∼⟪x⟫
          (suc (suc i)) → ⟦ρ⟧∼⟪ρ⟫ i

      ⟦rec⟧ = rec ⟦s⟧ ⟦z⟧
      ⟪rec⟫ = rec (⟪s⟫ ∘ ret) ⟪z⟫

      ⟦rec⟧∼⟪rec⟫ : (k : ℕ) → α ⊨ σ ∋ ⟦rec⟧ k ∼ ⟪rec⟫ k
      ⟦rec⟧∼⟪rec⟫ zero = ⟦z⟧∼⟪z⟫
      ⟦rec⟧∼⟪rec⟫ (suc k) = ⟦s⟧∼⟪s⟫ k (ret k) refl (⟦rec⟧ k) (⟪rec⟫ k) (⟦rec⟧∼⟪rec⟫ k)

      aux : (x : ℕ) → ret (⟪rec⟫ x) ≡ rec (λ x → ret ∘ ⟪s⟫ (ret x) ∘ Alg.alg ⟪ σ ⟫) (ret ⟪z⟫) x
      aux zero = refl
      aux (suc x) =
        ≡.cong
         (ret ∘ ⟪s⟫ (ret x))
         (≡.inv
          (≡.seq
           (≡.cong
            (Alg.alg ⟪ σ ⟫)
            (≡.inv (aux x)))
           (Alg.law/η ⟪ σ ⟫ (⟪rec⟫ x))))


  hauptsatz α (ν i q) ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫ =
    ≡.ind
     (λ σ q → α ⊨ σ ∋ ≡.use ⟦ρ⟧ i by ≡.cong ⟦_⟧ q ∎ ∼ ≡.use ⟪ρ⟫ i by ≡.cong (U ∘ ⟪_⟫) q ∎)
     (⟦ρ⟧∼⟪ρ⟫ i)
     (≡.inv q)

  hauptsatz α (ƛ f) ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫ ⟦s⟧ ⟪s⟫ ⟦s⟧∼⟪s⟫ =
    hauptsatz α f _ _ λ where
      zero → ⟦s⟧∼⟪s⟫
      (suc i) → ⟦ρ⟧∼⟪ρ⟫ i

  hauptsatz α (s · t) ⟦ρ⟧ ⟪ρ⟫ ⟦ρ⟧∼⟪ρ⟫ =
    hauptsatz α s _ _ ⟦ρ⟧∼⟪ρ⟫ _ _
     (hauptsatz α t _ _ ⟦ρ⟧∼⟪ρ⟫)


  hauptsatz₀
    : {τ : Type}
    → (α : Point)
    → (t : ⋄ ⊢ᵀ τ)
    → α ⊨ τ ∋ tm⟦ t ⟧ ⟦⋄⟧ ∼ tm⟪ t ⟫ ⟪⋄⟫
  hauptsatz₀ α t =
    hauptsatz _ t ⟦⋄⟧ ⟪⋄⟫ λ ()
