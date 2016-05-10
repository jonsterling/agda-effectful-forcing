module System-T where

open import Prelude.Finite
open import Prelude.Natural
open import Prelude.List
open import Prelude.Monoidal hiding (_⇒_)
import Prelude.Inspect as I
open import Prelude.Path
open import Prelude.Decidable

open import Baire
open import Dialogue
open import Context

open import System-T.Syntax
open import System-T.Semantics

-- To convert an internal Baire-functional into a dialogue tree, apply it to the
-- generic point Ω!
⌈_⌉ : ∀ {𝔏} → 𝔏 ▹ ⋄ ⊢ᵀ (` nat ⇒ ` nat) ⇒ ` nat → 𝔅 Nat
⌈ m ⌉ = 𝔅.⟦ ⊢ᵀ-map 𝔏.-⇒TΩ m · Ω ⟧₀

⌈_⌉′ : 𝔏.TΩ ▹ ⋄ ⊢ᵀ (` nat ⇒ ` nat) ⇒ ` nat → 𝔅 Nat
⌈ m ⌉′  = 𝔅.⟦ m · Ω ⟧₀

-- Church encoded dialogue trees in System T
⌊𝔇⌋ : Type → Type → Type → Type → Type
⌊𝔇⌋ X Y Z A = (Z ⇒ A) ⇒ ((Y ⇒ A) ⇒ X ⇒ A) ⇒ A

⌊η⌋ : ∀ {X Y Z A} → ⊢ᵀ Z ⇒ ⌊𝔇⌋ X Y Z A
⌊η⌋ = ƛ ƛ ƛ ((ν (su ze)) · ν (su (su ze)))

⌊ϝ⌋ : ∀ {X Y Z A} → ⊢ᵀ (Y ⇒ ⌊𝔇⌋ X Y Z A) ⇒ X ⇒ ⌊𝔇⌋ X Y Z A
⌊ϝ⌋ = ƛ ƛ ƛ ƛ (ν ze · (ƛ (ν (su (su (su (su ze)))) · ν ze · ν (su (su ze)) · ν (su ze))) · ν (su (su ze)))

⌊𝔅⌋ : Type → Type → Type
⌊𝔅⌋ = ⌊𝔇⌋ (` nat) (` nat)

-- Begin internalizing the logical relations.
--
-- 1. We interpret base types 𝔟 as dialogue trees that eventually compute a 𝔟.
-- 2. At functional type, we proceed by recursion.
--
⌊𝒱⟦_⟧⌋ : Type → Type → Type
⌊𝒱⟦ ` b ⟧⌋ = ⌊𝔅⌋ (` b)
⌊𝒱⟦ σ ⇒ τ ⟧⌋ A = ⌊𝒱⟦ σ ⟧⌋ A ⇒ ⌊𝒱⟦ τ ⟧⌋ A

-- The type of Baire functionals is a functor
⌊map⌋ : ∀ {X Y A} → ⊢ᵀ (X ⇒ Y) ⇒ ⌊𝔅⌋ X A ⇒ ⌊𝔅⌋ Y A
⌊map⌋ = ƛ ƛ (ƛ (ν (su ze) · (ƛ (ν (su ze) · ((ν (su (su (su ze)))) · ν ze)))))

-- The type of baire functionals is a monad
⌊ext⌋ : ∀ {X Y A} → ⊢ᵀ (X ⇒ ⌊𝔅⌋ Y A) ⇒ ⌊𝔅⌋ X A ⇒ ⌊𝔅⌋ Y A
⌊ext⌋ = ƛ ƛ ƛ ƛ (ν (su (su ze)) · (ƛ (ν (su (su (su (su ze)))) · ν ze · ν (su (su ze)) · ν (su ze))) · ν ze)

-- We extend the monadic bind into the logical relation ⌊𝒱⟦_⟧⌋
⌊Ext[_]⌋ : ∀ {X A} (σ : Type) → ⊢ᵀ (X ⇒ ⌊𝒱⟦ σ ⟧⌋ A) ⇒ ⌊𝔅⌋ X A ⇒ ⌊𝒱⟦ σ ⟧⌋ A
⌊Ext[ ` _ ]⌋ = ⌊ext⌋
⌊Ext[ σ ⇒ τ ]⌋ = ƛ ƛ ƛ (⌊Ext[ τ ]⌋ · (ƛ (ν (su (su (su ze))) · ν ze · ν (su ze))) · ν (su ze))

-- We show that all closed terms are (internally) in the logical relation
⌊𝔅⟦_⟧⌋ : ∀ {𝔏 m n σ A} {Γ : Ctx m} {Δ : Ctx n} → 𝔏 ▹ Γ ⊢ᵀ σ → ((i : Fin m) → 𝔏 ▹ Δ ⊢ᵀ ⌊𝒱⟦ Γ [ i ] ⟧⌋ A) → 𝔏 ▹ Δ ⊢ᵀ ⌊𝒱⟦ σ ⟧⌋ A
⌊𝔅⟦ zero ⟧⌋ ρ = ⌊η⌋ · zero
⌊𝔅⟦ succ ⟧⌋ ρ = ⌊map⌋ · succ
⌊𝔅⟦ rec[ σ ] ⟧⌋ ρ = ƛ ƛ (⌊Ext[ σ ]⌋ · (rec[ _ ] · (ƛ (ν (su (su ze)) · (⌊η⌋ · ν ze))) · ν ze))
⌊𝔅⟦ ν i ⟧⌋ ρ = ρ i
⌊𝔅⟦ ƛ t ⟧⌋ ρ = ƛ (⌊𝔅⟦ t ⟧⌋ (λ { ze → ν ze ; (su i) → wk (ρ i) }))
⌊𝔅⟦ m · n ⟧⌋ ρ = ⌊𝔅⟦ m ⟧⌋ ρ · ⌊𝔅⟦ n ⟧⌋ ρ
⌊𝔅⟦ Ω ⟧⌋ ρ = ⌊Ext[ ` nat ]⌋ · (⌊ϝ⌋ · ⌊η⌋)

generic : ∀ {A} → ⊢ᵀ ⌊𝒱⟦ ` nat ⇒ ` nat ⟧⌋ A
generic = ⌊ext⌋ · (⌊ϝ⌋ · ⌊η⌋)

-- Every T-definable Baire functional can be quoted into a T-definable dialogue tree
-- by applying it to the generic point.
--
-- Note that this operation is only available for closed terms. This operation cannot be
-- fully internalized into System T, because it is not extensional.
⌊⌈_⌉⌋ : ∀ {𝔏 A} → 𝔏 ▹ ⋄ ⊢ᵀ (` nat ⇒ ` nat) ⇒ (` nat) → 𝔏 ▹ ⋄ ⊢ᵀ ⌊𝔅⌋ (` nat) A
⌊⌈ t ⌉⌋ = ⌊𝔅⟦ t ⟧⌋ (λ { () }) · generic

_⇔_ : Set → Set → Set
P ⇔ Q = (P → Q) ⊗ (Q → P)

take : Nat → Point → Neigh
take ze α = []
take (su_ i) α = α i ∷ take i (λ x → α (su x))

bar-statement : Set₁
bar-statement =
  (φ : Neigh → Set)
  ([φ] : 𝔏.TΩ ▹ ⋄ ⊢ᵀ (` nat ⇒ ` nat) ⇒ ` nat)
    → (∀ α → φ (take (TΩ.⟦ [φ] · Ω ⟧₀ α) α))
    → (∀ U x → φ U → φ (x ∷ U))
    → (ψ : Neigh → Set)
    → (∀ U → φ U → ψ U)
    → (∀ U → (∀ i → ψ (i ∷ U)) → ψ U)
    → ∀ U → ψ U

pt : Neigh → Point
pt [] _ = ze
pt (x ∷ U) ze = x
pt (x ∷ U) (su_ i) = pt U i

postulate
  coh : ∀ {𝔏} α (t : 𝔏 ▹ ⋄ ⊢ᵀ ` nat) → TΩ.⟦ t ⟧₀ α ≡ 𝔇[ 𝔅.⟦ t ⟧₀ ] α

data ⊢_◃_ (U : Neigh) (φ : Neigh → Set) : Set where
  -- [U] is secured.
  η : φ U → ⊢ U ◃ φ

  -- [U] is securable because all of its immediate children are securable.
  ϝ : (∀ x → ⊢ (x ∷ U) ◃ φ) → ⊢ U ◃ φ

quote-nat : Nat → ⊢ᵀ ` nat
quote-nat ze = zero
quote-nat (su_ x) = succ · quote-nat x

insert : Point → Nat → Nat → Point
insert α ze x ze = x
insert α ze x (su_ j) = α j
insert α (su_ i) x ze = α ze
insert α (su_ i) x (su_ j) = insert α i x j

insert-law : ∀ α i x → insert α i x i ≡ x
insert-law α ze x = refl
insert-law α (su_ i) x = insert-law α i x

data _≼_ : Neigh → Point → Set where
  [] : ∀ {α} → [] ≼ α
  _∷_ : ∀ {α x U} → U ≼ α → α (List.len U) ≡ x → (x ∷ U) ≼ α

module BarTheorem
  (φ : Neigh → Set)
  (φ? : ∀ U → Decidable (φ U))
  (is-mono : ∀ U x → φ U → φ (x ∷ U))
  where
    annotate
      : (U : Neigh)
      → (δ : 𝔅 Nat)
      → (is-bar : ∀ α → U ≼ α → φ (take (𝔇[ δ ] α) α))
      → ⊢ U ◃ φ
    annotate U (η x) is-bar = {!!}
    annotate U (ϝ κ i) is-bar =
      ϝ λ j →
        annotate (j ∷ U) (κ i) λ α x →
          {!!}

⌊id⌋ : ∀ {τ} → ⊢ᵀ τ ⇒ τ
⌊id⌋ = ƛ ν ze

⌊max⌋ : ⊢ᵀ ` nat ⇒ ` nat ⇒ ` nat
⌊max⌋ = rec[ ` nat ⇒ ` nat ] · (ƛ ƛ (rec[ ` nat ] · (ƛ ƛ (succ · (ν (su (su ze)) · ν (su ze)))) · (succ · ν (su ze)))) · ⌊id⌋

⌊tree-𝔐⌋ : ⊢ᵀ (⌊𝔅⌋ (` nat) ((` nat ⇒ ` nat) ⇒ ` nat)) ⇒ (` nat ⇒ ` nat) ⇒ ` nat
⌊tree-𝔐⌋ = ƛ (ν ze · ƛ ƛ zero · ƛ ƛ ƛ (⌊max⌋ · (succ · ν (su ze)) · (ν (su (su ze)) · (ν ze · ν (su ze)) · ν ze)))

⌊𝔐[_]⌋
  : ∀ {𝔏}
  → 𝔏 ▹ ⋄ ⊢ᵀ (` nat ⇒ ` nat) ⇒ ` nat
  → 𝔏 ▹ ⋄ ⊢ᵀ (` nat ⇒ ` nat) ⇒ ` nat
⌊𝔐[ t ]⌋ =
  ⌊tree-𝔐⌋ · ⌊⌈ t ⌉⌋
