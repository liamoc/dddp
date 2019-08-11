module Trip.Semantics(State : Set) where
  open import Trip.Core(State)
  open import Data.Product
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Data.Sum hiding ([_,_])
  open import Function


  variable σ₁ σ σ₂ σ₃ : State

  StateRel = State → State → Set

  _⦂_ : StateRel → StateRel → StateRel
  (R ⦂ S) σ₁ σ₃ = ∃[ σ₂ ] (R σ₁ σ₂ × S σ₂ σ₃)
  _∪_ : StateRel → StateRel → StateRel
  (R ∪ S) σ₁ σ₂ = R σ₁ σ₂ ⊎ S σ₁ σ₂

  data _⋆ (R : StateRel) : StateRel where
    refl : (R ⋆) σ σ
    step : R σ₁ σ₂ → (R ⋆) σ₂ σ₃ → (R ⋆) σ₁ σ₃

  ⟦_⟧u : (Σ: ϕ → Σ: ψ) → StateRel
  ⟦_⟧u u σ₁ σ₂ = ∀ prf-ϕ → let σ₂′ , _ = u (σ₁ , prf-ϕ)
                            in  σ₂ ≡ σ₂′

  ⟦_⟧g :  Assertion → StateRel
  ⟦ g ⟧g σ₁ σ₂ = g ⦃ σ₁ ⦄ × σ₁ ≡ σ₂

  ⟦_⟧ : [ ϕ , ψ ] → StateRel
  ⟦ SEQ P Q ⟧ = ⟦ P ⟧ ⦂ ⟦ Q ⟧
  ⟦ CHO P Q ⟧ = ⟦ P ⟧ ∪ ⟦ Q ⟧
  ⟦ UPD x ⟧   = ⟦ x ⟧u
  ⟦ STAR P ⟧  = ⟦ P ⟧ ⋆
  ⟦ GUARD g ⟧ = ⟦ g ⟧g


  sound : (P : [ ϕ , ψ ])
        → ⟦ P ⟧ σ₁ σ₂ → ϕ  ⦃ σ₁ ⦄ → ψ ⦃ σ₂ ⦄
  sound (SEQ P Q) (_ , p , q) = sound Q q ∘ sound P p
  sound (CHO P Q) (inj₁ p)    = sound P p
  sound (CHO P Q) (inj₂ q)    = sound Q q
  sound (STAR P) (step p ps)  = sound (STAR P) ps ∘ sound P p
  sound (STAR P) refl         = id
  sound (GUARD g) (p , refl)  = _$ p
  sound (UPD x) (p)           = sound-upd x p
    where
      sound-upd : (u : Σ: ϕ → Σ: ψ)
                → ⟦ u ⟧u σ₁ σ₂ → ϕ ⦃ σ₁ ⦄ → ψ ⦃ σ₂ ⦄
      sound-upd u sem prf-ϕ
       with u (_ , prf-ϕ) | sem prf-ϕ
      ... | _ , prf-ψ     | refl       = prf-ψ
