module system-t where

open import Prelude.Finite
open import Prelude.Functor
open import Prelude.Monad
open import Prelude.Natural
open import Prelude.String
open import Prelude.Monoidal hiding (_⇒_)

open Π using (_∘_)

open import Baire
open import Dialogue
open import Context

data type : Set where
  nat : type
  atom : type
  _⇒_ : type → type → type

infixr 6 _⇒_

Ctx : Nat → Set
Ctx n = type ^ n

module Lang where
  data Ob : Set where
    T : Ob
    TΩ : Ob

  data Hom : Ob → Ob → Set where
    T⇒T : Hom T T
    -⇒TΩ : ∀ {𝔏} → Hom 𝔏 TΩ

open Lang using (T; TΩ; T⇒T; -⇒TΩ)

data _▹_⊢ᵀ_ {n : Nat} : (𝔏 : Lang.Ob) (Γ : Ctx n) → type → Set where
  tok : {𝔏 : _} {Γ : Ctx n} → String → 𝔏 ▹ Γ ⊢ᵀ atom
  ze : {𝔏 : _} {Γ : Ctx n} → 𝔏 ▹ Γ ⊢ᵀ nat
  su : {𝔏 : _} {Γ : Ctx n} → 𝔏 ▹ Γ ⊢ᵀ nat ⇒ nat
  rec : {𝔏 : _} {Γ : Ctx n} {σ : type} → 𝔏 ▹ Γ ⊢ᵀ (nat ⇒ σ ⇒ σ) ⇒ σ ⇒ nat ⇒ σ
  ν : {𝔏 : _} {Γ : Ctx n} → (i : Fin n) → 𝔏 ▹ Γ ⊢ᵀ Γ [ i ]
  ƛ_ : {𝔏 : _} {Γ : Ctx n} {σ τ : type} → 𝔏 ▹ Γ , σ ⊢ᵀ τ → 𝔏 ▹ Γ ⊢ᵀ σ ⇒ τ
  _·_ : {𝔏 : _} {Γ : Ctx n} {σ τ : type} → 𝔏 ▹ Γ ⊢ᵀ (σ ⇒ τ) → 𝔏 ▹ Γ ⊢ᵀ σ → 𝔏 ▹ Γ ⊢ᵀ τ
  Ω : {Γ : Ctx n} → TΩ ▹ Γ ⊢ᵀ nat ⇒ nat

infixl 1 _·_
infixr 3 _▹_⊢ᵀ_

⊢ᵀ-map : ∀ {𝔏₀ 𝔏₁ n τ} {Γ : Ctx n} → Lang.Hom 𝔏₀ 𝔏₁ → 𝔏₀ ▹ Γ ⊢ᵀ τ → 𝔏₁ ▹ Γ ⊢ᵀ τ
⊢ᵀ-map T⇒T tm = tm
⊢ᵀ-map -⇒TΩ (tok x) = tok x
⊢ᵀ-map -⇒TΩ ze = ze
⊢ᵀ-map -⇒TΩ su = su
⊢ᵀ-map -⇒TΩ rec = rec
⊢ᵀ-map -⇒TΩ (ν i) = ν i
⊢ᵀ-map -⇒TΩ (ƛ e) = ƛ ⊢ᵀ-map -⇒TΩ e
⊢ᵀ-map -⇒TΩ (f · m) = ⊢ᵀ-map -⇒TΩ f · ⊢ᵀ-map -⇒TΩ m
⊢ᵀ-map -⇒TΩ Ω = Ω

id : {ℓ : _} {A : Set ℓ} → A → A
id x = x

𝒱⟦_⟧ : type → (Set → Set) → Set
𝒱⟦ nat ⟧ f = f Nat
𝒱⟦ atom ⟧ f = f String
𝒱⟦ σ ⇒ τ ⟧ f = 𝒱⟦ σ ⟧ f → 𝒱⟦ τ ⟧ f

𝒢⟦_⟧ : {n : Nat} → Ctx n → (Set → Set) → Set
𝒢⟦ Γ ⟧ f = (i : Fin _) → 𝒱⟦ Γ [ i ] ⟧ f

⟦⋄⟧ : ∀ {f} → 𝒢⟦ ⋄ ⟧ f
⟦⋄⟧ ()

_⟦,⟧_ : ∀ {f n} {Γ : Ctx n} {σ : type} → 𝒢⟦ Γ ⟧ f → 𝒱⟦ σ ⟧ f → 𝒢⟦ Γ , σ ⟧ f
(ρ ⟦,⟧ x) ze = x
(ρ ⟦,⟧ x) (su_ i) = ρ i

Rec : {X : Set} → (Nat → X → X) → X → Nat → X
Rec f x ze = x
Rec f x (su_ n) = f n (Rec f x n)

Ext : {X : Set} {τ : type} → (X → 𝒱⟦ τ ⟧ 𝔅) → 𝔅 X → 𝒱⟦ τ ⟧ 𝔅
Ext {τ = nat} f x = x ≫= f
Ext {τ = atom} f x = x ≫= f
Ext {τ = σ ⇒ τ} g δ s = Ext {τ = τ} (λ x → g x s) δ

_⊩⟦_⟧_ : ∀ {𝔏 n τ} {Γ : Ctx n} → Point → 𝔏 ▹ Γ ⊢ᵀ τ → 𝒢⟦ Γ ⟧ id → 𝒱⟦ τ ⟧ id
α ⊩⟦ tok x ⟧ ρ = x
α ⊩⟦ ze ⟧ ρ = ze
α ⊩⟦ su ⟧ ρ = su_
α ⊩⟦ rec ⟧ ρ = Rec
α ⊩⟦ ν i ⟧ ρ = ρ i
α ⊩⟦ ƛ e ⟧ ρ = λ x → α ⊩⟦ e ⟧ (ρ ⟦,⟧ x)
α ⊩⟦ m · n ⟧ ρ = (α ⊩⟦ m ⟧ ρ) (α ⊩⟦ n ⟧ ρ)
α ⊩⟦ Ω ⟧ ρ = α

𝔅⟦_⟧ : ∀ {n τ} {Γ : Ctx n} → TΩ ▹ Γ ⊢ᵀ τ → 𝒢⟦ Γ ⟧ 𝔅 → 𝒱⟦ τ ⟧ 𝔅
𝔅⟦ tok x ⟧ _ = η x
𝔅⟦ ze ⟧ _ = η ze
𝔅⟦ su ⟧ _ = map su_
𝔅⟦ rec {σ = σ} ⟧ _ s z = Ext {τ = σ} (Rec (s ∘ η) z)
𝔅⟦ ν i ⟧ ρ = ρ i
𝔅⟦ ƛ e ⟧ ρ = λ x → 𝔅⟦ e ⟧ (ρ ⟦,⟧ x)
𝔅⟦ m · n ⟧ ρ = 𝔅⟦ m ⟧ ρ (𝔅⟦ n ⟧ ρ)
𝔅⟦ Ω ⟧ _ = Ext {τ = nat} (ϝ η)

-- To convert an internal Baire-functional into a dialogue tree, apply it to the
-- generic point Ω!
⌈_⌉ : {𝔏 : _} → 𝔏 ▹ ⋄ ⊢ᵀ (nat ⇒ nat) ⇒ nat → 𝔅 Nat
⌈ m ⌉ = 𝔅⟦ ⊢ᵀ-map -⇒TΩ m · Ω ⟧ ⟦⋄⟧

-- TODO: church encode dialogue trees in System T and internalize the modulus of continuity,
-- as in http://www.cs.bham.ac.uk/~mhe/dialogue/church-dialogue-internal.html

⊢ᵀ_ : type → Set
⊢ᵀ τ = ∀ {𝔏 n} {Γ : Ctx n} → 𝔏 ▹ Γ ⊢ᵀ τ

infixr 3 ⊢ᵀ_

-- Church encoded dialogue trees in System T
⌊𝔇⌋ : type → type → type → type → type
⌊𝔇⌋ X Y Z A = (Z ⇒ A) ⇒ ((Y ⇒ A) ⇒ X ⇒ A) ⇒ A

⌊η⌋ : ∀ {X Y Z A} → ⊢ᵀ Z ⇒ ⌊𝔇⌋ X Y Z A
⌊η⌋ = ƛ ƛ ƛ ((ν (su_ ze)) · ν (su_ (su_ ze)))

⌊ϝ⌋ : ∀ {X Y Z A} → ⊢ᵀ (Y ⇒ ⌊𝔇⌋ X Y Z A) ⇒ X ⇒ ⌊𝔇⌋ X Y Z A
⌊ϝ⌋ = ƛ ƛ ƛ ƛ (ν ze · (ƛ (ν (su_ (su_ (su_ (su_ ze)))) · ν ze · ν (su_ (su_ ze)) · ν (su_ ze))) · ν (su_ (su_ ze)))

⌊𝔅⌋ : type → type → type
⌊𝔅⌋ = ⌊𝔇⌋ nat nat

⌊map⌋ : ∀ {X Y A} → ⊢ᵀ (X ⇒ Y) ⇒ ⌊𝔅⌋ X A ⇒ ⌊𝔅⌋ Y A
⌊map⌋ = ƛ ƛ (ƛ (ν (su_ ze) · (ƛ (ν (su_ ze) · ((ν (su_ (su_ (su_ ze)))) · ν ze)))))

⌊ext⌋ : ∀ {X Y A} → ⊢ᵀ (X ⇒ ⌊𝔅⌋ Y A) ⇒ ⌊𝔅⌋ X A ⇒ ⌊𝔅⌋ Y A
⌊ext⌋ = ƛ ƛ ƛ ƛ (ν (su_ (su_ ze)) · (ƛ (ν (su_ (su_ (su_ (su_ ze)))) · ν ze · ν (su_ (su_ ze)) · ν (su_ ze))) · ν ze)

⌊𝔅⟦_⟧⌋ : type → type → type
⌊𝔅⟦ nat ⟧⌋ = ⌊𝔅⌋ nat
⌊𝔅⟦ atom ⟧⌋ = ⌊𝔅⌋ atom
⌊𝔅⟦ σ ⇒ τ ⟧⌋ A = ⌊𝔅⟦ σ ⟧⌋ A ⇒ ⌊𝔅⟦ τ ⟧⌋ A

⌊Ext⌋ : ∀ {X A σ} → ⊢ᵀ (X ⇒ ⌊𝔅⟦ σ ⟧⌋ A) ⇒ ⌊𝔅⌋ X A ⇒ ⌊𝔅⟦ σ ⟧⌋ A
⌊Ext⌋ {σ = nat} = ⌊ext⌋
⌊Ext⌋ {σ = atom} = ⌊ext⌋
⌊Ext⌋ {σ = σ ⇒ τ} = ƛ ƛ ƛ (⌊Ext⌋ {σ = τ} · (ƛ (ν (su_ (su_ (su_ ze))) · ν ze · ν (su_ ze))) · ν (su_ ze))

max : {𝔏 : _} → 𝔏 ▹ ⋄ ⊢ᵀ nat ⇒ nat ⇒ nat
max = {!!}
