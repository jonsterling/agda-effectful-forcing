module System-T where

open import Prelude.Finite
open import Prelude.Natural

open import Baire
open import Dialogue
open import Context

open import System-T.Syntax
open import System-T.Semantics


-- To convert an internal Baire-functional into a dialogue tree, apply it to the
-- generic point Ω!
⌈_⌉ : ⋄ ⊢ᵀ (` nat ⇒ ` nat) ⇒ ` nat → 𝔅 Nat
⌈ m ⌉ = 𝔅.⟦ ⊢ᵀ-map {𝔏.T} 𝔏.-⇒TΩ m · Ω ⟧ 𝔅.𝒢.⋄

-- TODO: internalizing modulus of continuity via church encoding of dialogues:
-- http://www.cs.bham.ac.uk/~mhe/dialogue/church-dialogue-internal.html

-- Church encoded dialogue trees in System T
⌊𝔇⌋ : Type → Type → Type → Type → Type
⌊𝔇⌋ X Y Z A = (Z ⇒ A) ⇒ ((Y ⇒ A) ⇒ X ⇒ A) ⇒ A

⌊η⌋ : ∀ {X Y Z A} → ⊢ᵀ Z ⇒ ⌊𝔇⌋ X Y Z A
⌊η⌋ = ƛ ƛ ƛ ((ν (su ze)) · ν (su (su ze)))

⌊ϝ⌋ : ∀ {X Y Z A} → ⊢ᵀ (Y ⇒ ⌊𝔇⌋ X Y Z A) ⇒ X ⇒ ⌊𝔇⌋ X Y Z A
⌊ϝ⌋ = ƛ ƛ ƛ ƛ (ν ze · (ƛ (ν (su (su (su (su ze)))) · ν ze · ν (su (su ze)) · ν (su ze))) · ν (su (su ze)))

⌊𝔅⌋ : Type → Type → Type
⌊𝔅⌋ = ⌊𝔇⌋ (` nat) (` nat)

⌊map⌋ : ∀ {X Y A} → ⊢ᵀ (X ⇒ Y) ⇒ ⌊𝔅⌋ X A ⇒ ⌊𝔅⌋ Y A
⌊map⌋ = ƛ ƛ (ƛ (ν (su ze) · (ƛ (ν (su ze) · ((ν (su (su (su ze)))) · ν ze)))))

⌊ext⌋ : ∀ {X Y A} → ⊢ᵀ (X ⇒ ⌊𝔅⌋ Y A) ⇒ ⌊𝔅⌋ X A ⇒ ⌊𝔅⌋ Y A
⌊ext⌋ = ƛ ƛ ƛ ƛ (ν (su (su ze)) · (ƛ (ν (su (su (su (su ze)))) · ν ze · ν (su (su ze)) · ν (su ze))) · ν ze)

⌊𝒱⟦_⟧⌋ : Type → Type → Type
⌊𝒱⟦ ` b ⟧⌋ = ⌊𝔅⌋ (` b)
⌊𝒱⟦ σ ⇒ τ ⟧⌋ A = ⌊𝒱⟦ σ ⟧⌋ A ⇒ ⌊𝒱⟦ τ ⟧⌋ A

⌊Ext[_]⌋ : ∀ {X A} (σ : Type) → ⊢ᵀ (X ⇒ ⌊𝒱⟦ σ ⟧⌋ A) ⇒ ⌊𝔅⌋ X A ⇒ ⌊𝒱⟦ σ ⟧⌋ A
⌊Ext[ ` _ ]⌋ = ⌊ext⌋
⌊Ext[ σ ⇒ τ ]⌋ = ƛ ƛ ƛ (⌊Ext[ τ ]⌋ · (ƛ (ν (su (su (su ze))) · ν ze · ν (su ze))) · ν (su ze))

⌊zero⌋ : ∀ {A} → ⊢ᵀ ⌊𝔅⌋ (` nat) A
⌊zero⌋ = ⌊η⌋ · zero

⌊rec[_]⌋ : ∀ σ {A} → ⊢ᵀ (⌊𝒱⟦ ` nat ⟧⌋ A ⇒ ⌊𝒱⟦ σ ⟧⌋ A ⇒ ⌊𝒱⟦ σ ⟧⌋ A) ⇒ ⌊𝒱⟦ σ ⟧⌋ A ⇒ ⌊𝔅⌋ (` nat) A ⇒ ⌊𝒱⟦ σ ⟧⌋ A
⌊rec[ σ ]⌋ = ƛ ƛ (⌊Ext[ σ ]⌋ · (rec[ _ ] · (ƛ (ν (su (su ze)) · (⌊η⌋ · ν ze))) · ν ze))

⌊𝔅⟦_⟧⌋ : ∀ {𝔏 m n σ A} {Γ : Ctx m} {Δ : Ctx n} → 𝔏 ▹ Γ ⊢ᵀ σ → ((i : Fin m) → 𝔏 ▹ Δ ⊢ᵀ ⌊𝒱⟦ Γ [ i ] ⟧⌋ A) → 𝔏 ▹ Δ ⊢ᵀ ⌊𝒱⟦ σ ⟧⌋ A
⌊𝔅⟦ tok x ⟧⌋ ρ = ⌊η⌋ · tok x
⌊𝔅⟦ zero ⟧⌋ ρ = ⌊η⌋ · zero
⌊𝔅⟦ succ ⟧⌋ ρ = ⌊map⌋ · succ
⌊𝔅⟦ rec[ σ ] ⟧⌋ ρ = ⌊rec[ σ ]⌋
⌊𝔅⟦ ν i ⟧⌋ ρ = ρ i
⌊𝔅⟦ ƛ t ⟧⌋ ρ = ƛ (⌊𝔅⟦ t ⟧⌋ (λ { ze → ν ze ; (su i) → wk (ρ i) }))
⌊𝔅⟦ m · n ⟧⌋ ρ = ⌊𝔅⟦ m ⟧⌋ ρ · ⌊𝔅⟦ n ⟧⌋ ρ
⌊𝔅⟦ Ω ⟧⌋ ρ = ⌊Ext[ ` nat ]⌋ · (⌊ϝ⌋ · ⌊η⌋)

-- Every T-definable Baire functional can be quoted into a T-definable dialogue tree.
-- Note that this operation is only available for closed terms. This operation cannot be
-- fully internalized into System T, because it is not extensional.
⌊⌈_⌉⌋ : ∀ {𝔏 A} → 𝔏 ▹ ⋄ ⊢ᵀ (` nat ⇒ ` nat) ⇒ (` nat) → 𝔏 ▹ ⋄ ⊢ᵀ ⌊𝔅⌋ (` nat) A
⌊⌈ t ⌉⌋ = ⌊𝔅⟦ t ⟧⌋ (λ { () }) · (⌊ext⌋ · (⌊ϝ⌋ · ⌊η⌋))

-- TODO! this is a pain in the neck to define!
⌊max⌋ : ⊢ᵀ ` nat ⇒ ` nat ⇒ ` nat
⌊max⌋ = ƛ {!!}

⌊tree-𝔐⌋ : ⊢ᵀ (⌊𝔅⌋ (` nat) ((` nat ⇒ ` nat) ⇒ ` nat)) ⇒ (` nat ⇒ ` nat) ⇒ ` nat
⌊tree-𝔐⌋ = ƛ (ν ze · ƛ ƛ zero · ƛ ƛ ƛ (⌊max⌋ · (succ · ν (su ze)) · (ν (su (su ze)) · (ν ze · ν (su ze)) · ν ze)))

⌊𝔐[_]⌋
  : ∀ {𝔏}
  → 𝔏 ▹ ⋄ ⊢ᵀ (` nat ⇒ ` nat) ⇒ ` nat
  → 𝔏 ▹ ⋄ ⊢ᵀ (` nat ⇒ ` nat) ⇒ ` nat
⌊𝔐[ t ]⌋ =
  ⌊tree-𝔐⌋ · ⌊⌈ t ⌉⌋
