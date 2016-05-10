module System-T where

open import Prelude.Finite
open import Prelude.Natural
open import Prelude.List
open import Prelude.Monoidal hiding (_⇒_)
import Prelude.Inspect as I
open import Prelude.Maybe
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

head : Point → Nat
head α = α 0

tail : Point → Point
tail α i = α (su i)

_⌢_ : List Nat → Nat → List Nat
[] ⌢ x = x ∷ []
(x ∷ U) ⌢ y = x ∷ (U ⌢ y)

take : Nat → Point → List Nat
take ze α = []
take (su n) α = head α ∷ take n (tail α)

pt : List Nat → Point
pt [] i = 0
pt (x ∷ U) ze = x
pt (x ∷ U) (su_ i) = pt U i

take-pt-id : ∀ U → take (List.len U) (pt U) ≡ U
take-pt-id [] = refl
take-pt-id (x ∷ U) rewrite take-pt-id U = refl

take-pt-snoc-id : ∀ U y → take (List.len U) (pt (U ⌢ y)) ≡ U
take-pt-snoc-id [] _ = refl
take-pt-snoc-id (x ∷ U) y rewrite take-pt-snoc-id U y = refl

data ⊢_◃_ : (U : List Nat) (φ : List Nat → Set) → Set where
  η : ∀ {φ U} → φ U → ⊢ U ◃ φ
  ζ : ∀ {φ U x} → ⊢ U ◃ φ → ⊢ U ⌢ x ◃ φ
  ϝ : ∀ {φ U} → (∀ x → ⊢ U ⌢ x ◃ φ) → ⊢ U ◃ φ

data ⊩_◃_ : (U : List Nat) (φ : List Nat → Set) → Set where
  η : ∀ {φ U} → φ U → ⊩ U ◃ φ
  ϝ : ∀ {φ U} → (∀ x → ⊩ U ⌢ x ◃ φ) → ⊩ U ◃ φ

monotone : (φ : List Nat → Set) → Set
monotone φ = ∀ {U x} → φ U → φ (U ⌢ x)

module Normalize {φ : List Nat → Set} (φ-mono : monotone φ) where
  ⊩-mono : monotone (⊩_◃ φ)
  ⊩-mono (η x) = η (φ-mono x)
  ⊩-mono (ϝ κ) = ϝ λ x → ⊩-mono (κ _)

  eval : ∀ {U} → ⊢ U ◃ φ → ⊩ U ◃ φ
  eval (η x) = η x
  eval (ζ p) = ⊩-mono (eval p)
  eval (ϝ κ) = ϝ (λ x → eval (κ x))

  quo : ∀ {U} → ⊩ U ◃ φ → ⊢ U ◃ φ
  quo (η x) = η x
  quo (ϝ κ) = ϝ λ x → quo (κ x)

  norm : ∀ {U} → ⊢ U ◃ φ → ⊢ U ◃ φ
  norm x = quo (eval x)

data _∈_ : Point → List Nat → Set where
  stop : ∀ {α} → α ∈ []
  step : ∀ {α U} → tail α ∈ U → α ∈ (head α ∷ U)

postulate
  pt-∈ : ∀ U → pt U ∈ U

infixr 3 _∈_

module BarTheorem
  (φ : List Nat → Set)
  (φ? : ∀ U → Decidable (φ U))
  (mono : monotone φ)
  where
    mono◃⋆ : ∀ V → ⊢ [] ◃ φ → ⊢ V ◃ φ
    mono◃⋆ = {!!}

    mono⋆ : ∀ V → φ [] → φ V
    mono⋆ = {!!}

    open Normalize {φ} mono

    data in-bounds : List Nat → Nat → Set where
      in-bounds-ze : ∀ {U x n} → n ≡ List.len U → in-bounds (U ⌢ x) n
      in-bounds-su : ∀ {U i x} → in-bounds U (su i) → in-bounds (U ⌢ x) i

    data out-bounds : List Nat → Nat → Set where
      out-bounds-[] : ∀ {i} → out-bounds [] i
      out-bounds-∷ : ∀ {U i x} → out-bounds U i → out-bounds (x ∷ U) (su i)

    data bounds (U : List Nat) (i : Nat) : Set where
      is-in-bounds : in-bounds U i → bounds U i
      is-out-bounds : out-bounds U i → bounds U i

    compute-bounds : (U : List Nat) (i : Nat) → bounds U i
    compute-bounds = {!!}

    take-snoc-lemma : ∀ α i → take (su i) α ≡ take i α ⌢ α i
    take-snoc-lemma α ze = refl
    take-snoc-lemma α (su_ i) rewrite take-snoc-lemma (tail α) i = refl

    postulate
      bounds-lem : ∀ {U} n x → in-bounds U (su n) → take n (pt U) ≡ take n (pt (U ⌢ x))
      -- Informal proof:
      -- By hypothesis, we have [su n < | U |]; therefore, the first n items of all extensions of
      -- U will be the same, because they will be a prefix of U itself.

    lemma : {U : List Nat} {n : Nat} → in-bounds U n → ⊩ (take n (pt U)) ◃ φ  → ⊢ U ◃ φ
    lemma (in-bounds-ze {U = U} {x = x} h) p = ζ (quo p′)
      where
        p′ : ⊩ U ◃ φ
        p′ rewrite take-pt-snoc-id U x ≡.⁻¹ | h ≡.⁻¹ = p
    lemma {n = n} (in-bounds-su {U = U} {x = x} b) p = ζ (lemma b (eval p′))
      where
        p′ : ⊢ take (su n) (pt U) ◃ φ
        p′ rewrite take-snoc-lemma (pt U) n | bounds-lem n x b = ζ (quo p)

    annotate
      : (U : List Nat)
      → (δ : 𝔅 Nat)
      → (is-bar : ∀ α → α ∈ U → φ (take (𝔇[ δ ] α) α))
      → ⊢ U ◃ φ
    annotate U (η n) is-bar with compute-bounds U n
    annotate U (η n) is-bar | is-in-bounds b = lemma b (η (is-bar (pt U) (pt-∈ U)))
    annotate U (η n) is-bar | is-out-bounds x = {!!}

    annotate U (ϝ κ i) is-bar =
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
