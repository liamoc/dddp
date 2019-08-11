module Trip.Surface(Σ : Set) where
  open import Trip.Core(Σ)
  open import Delay

  open import Function
  open import Relation.Nullary
  open import Data.Product

  _﹕_ : Delay [ ϕ , α ]
      → Delay [ α , ψ ]
      → Delay [ ϕ , ψ ]
  P ﹕ Q = ⦇ SEQ P Q ⦈

  if_then_else_fi : (g : Assertion)
                  → Delay [ ϕ × g , ψ ]
                  → Delay [ ϕ × ¬ g , ψ ]
                  → Delay [ ϕ , ψ ]
  if g then p else q fi = ⦇ (IFTHENELSE g) p q ⦈

  while_begin_end : (g : Assertion)
                  → Delay [ g × ϕ , ϕ ]
                  → Delay [ ϕ , ¬ g × ϕ ]
  while g begin P end = ⦇ (WHILE g) P ⦈

  assert : (ϕ : Assertion) → Delay [ ϕ , ψ ]
  assert ϕ = ⦇ CONS later ⦈


  guard : (g : Assertion) → Delay [ (g → ϕ) , ϕ ]
  guard g = pure (GUARD g)

  infixr 5 _﹕_

  upd : (Σ: ϕ → Σ: ψ) → Delay [ ϕ , ψ ]
  upd u = pure (UPD u)
