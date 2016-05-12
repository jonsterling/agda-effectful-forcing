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
open import Brouwer
open import Dialogue
open import Context
open import Snoc

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

module BarTheorem (φ : List Nat → Set) (mono : monotone φ) where
  open Normalize {φ} mono
  open Π using (_∘_)

  0⋯ : Point
  0⋯ _ = 0

  len-snoc-lemma-2 : ∀ {X : Set} (U : List X) {x} → su List.len U ≡ List.len (U ⌢ x)
  len-snoc-lemma-2 [] = refl
  len-snoc-lemma-2 (x ∷ U) {x = y} rewrite len-snoc-lemma-2 U {y} = refl

  len-snoc-lemma : ∀ {X : Set} (U : List X) {x n} → List.len (U ⌢ x) ≡ su n → List.len U ≡ n
  len-snoc-lemma [] refl = refl
  len-snoc-lemma (x₁ ∷ U) refl = len-snoc-lemma-2 U

  ≡-to-≤ : ∀ m n → n ≡ m → n Nat.≤ m
  ≡-to-≤ ze .0 refl = Nat.stop
  ≡-to-≤ (su_ x) .(su x) refl = Nat.stop

  lem : ∀ {U} δ → δ ⊨ U ◃ φ → ⊢ U ◃ φ
  lem {U} (η n) f = {!!}
    -- TODO:
    --   1. in case n > len(U), we are not yet in the bar; we must apply ϝ by (n - len(U)) times
    --   2. in case n == len(U), then we have just made it into the bar, and we apply η.
    --   3. in case n < len(U), we are already in the bar and need to apply ζ by (len(U) - n) times.
  lem {U} (ϝ κ) f =
    ϝ λ x →
      lem
        (κ x)
        (≡.coe* φ (cons-snoc-prepend-law U)
           ∘ f
           ∘ cons x)


  analyze
    : (U : List Nat) (δ : 𝔅ₙ Nat)
    → δ ⊨ U ◃ φ
    → ⊢ U ◃ φ
  analyze U (η x) is-bar = {!!}
  analyze U (ϝ κ) is-bar =
    ϝ λ x →
      analyze
        (U ⌢ x)
        (κ x)
        (≡.coe* φ (cons-snoc-prepend-law U)
          ∘ is-bar
          ∘ cons x)

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
