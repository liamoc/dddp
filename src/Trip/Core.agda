module Trip.Core(State : Set) where
  open import Data.Product
  open import Relation.Nullary
  open import Function


  Assertion = ⦃ σ : State ⦄ → Set

  Σ:_ : Assertion → Set
  Σ: ϕ = Σ State (λ σ → ϕ ⦃ σ ⦄)

  variable ϕ ϕ′ ψ ψ′ α : Assertion

  data [_,_] : Assertion → Assertion → Set₁ where
    SEQ   : [ ϕ , α ] → [ α , ψ ] → [ ϕ , ψ ]
    CHO   : [ ϕ , ψ ] → [ ϕ , ψ ] → [ ϕ , ψ ]
    UPD   : (Σ: ϕ → Σ: ψ) → [ ϕ , ψ  ]
    STAR  : [ ϕ , ϕ ] → [ ϕ , ϕ ]
    GUARD : (g : Assertion) → [ (g → ϕ) , ϕ ]



  Π:_ : Assertion → Set
  Π: ϕ = (∀ ⦃ σ : State ⦄ → ϕ ⦃ σ ⦄)

  CONS : Π: (ϕ → ψ) → [ ϕ , ψ ]
  CONS ϕ→ψ = UPD λ { ( σ , ϕ ) → σ , (ϕ→ψ ⦃ σ ⦄ ϕ) }

  SKIP : [ ϕ , ϕ ]
  SKIP = CONS (λ x → x)

  IFTHENELSE : (g : Assertion)
             → [ ϕ × g , ψ ]
             → [ ϕ × ¬ g , ψ  ]
             → [ ϕ , ψ ]
  IFTHENELSE g P Q
    = CHO (SEQ (SEQ (CONS _,_) (GUARD g)) P)
          (SEQ (SEQ (CONS _,_) (GUARD (¬ g))) Q)

  WHILE : (g : Assertion) → [ g × ϕ , ϕ ] → [ ϕ , ¬ g × ϕ ]
  WHILE g P = SEQ (STAR (SEQ (SEQ (CONS (flip _,_))
                                  (GUARD g))
                             P))
                  (SEQ (CONS (flip _,_))
                       (GUARD (¬ g)))
