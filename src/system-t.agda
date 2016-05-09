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

⌊𝔅⟦_⟧⌋ : Type → Type → Type
⌊𝔅⟦ ` b ⟧⌋ = ⌊𝔅⌋ (` b)
⌊𝔅⟦ σ ⇒ τ ⟧⌋ A = ⌊𝔅⟦ σ ⟧⌋ A ⇒ ⌊𝔅⟦ τ ⟧⌋ A

⌊Ext[_]⌋ : ∀ {X A} (σ : Type) → ⊢ᵀ (X ⇒ ⌊𝔅⟦ σ ⟧⌋ A) ⇒ ⌊𝔅⌋ X A ⇒ ⌊𝔅⟦ σ ⟧⌋ A
⌊Ext[ ` _ ]⌋ = ⌊ext⌋
⌊Ext[ σ ⇒ τ ]⌋ = ƛ ƛ ƛ (⌊Ext[ τ ]⌋ · (ƛ (ν (su (su (su ze))) · ν ze · ν (su ze))) · ν (su ze))

-- max : {𝔏 : _} → 𝔏 ▹ ⋄ ⊢ᵀ nat ⇒ nat ⇒ nat
-- max = {!!}
