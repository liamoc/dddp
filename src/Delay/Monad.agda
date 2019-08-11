module Delay.Monad where
  open import Function
  import Level
  open import Data.Unit
  open import Data.Product
  
  variable ℓ ℓ₁ ℓ₂ : Level.Level
  variable A B X : Set ℓ

  record MDelay (X : Set ℓ) : Set (Level.suc ℓ) where
     constructor Prf
     field
       goals : Set
       prove : goals → X

  open MDelay
  _<*>_ :  MDelay (A → B) → MDelay A → MDelay B
  d₁ <*> d₂ = Prf (goals d₁ × goals d₂)
                λ { (p₁ , p₂ ) → prove d₁ p₁ (prove d₂ p₂) }

  pure : X → MDelay X
  pure x = Prf ⊤ (const x)

  join : MDelay (MDelay A) → MDelay A
  join d = Prf (Σ (goals d) (goals ∘ prove d))
            λ { (g , g′) →  prove (prove d g) g′ }
