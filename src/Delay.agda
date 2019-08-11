module Delay where
  open import Data.List hiding ([_])
  open import Function

  infixr 5 _∷_
  data HList : List Set → Set where
    [] : HList []
    _∷_ : ∀{S}{SS} → S → HList SS → HList (S ∷ SS)

  import Level
  variable ℓ ℓ₁ ℓ₂ : Level.Level
  variable A B X : Set ℓ

  record Delay (X : Set ℓ) : Set (Level.suc ℓ) where
     constructor Prf
     field
       goals : List Set
       prove : HList goals → X

  structure:_proofs:_done = Delay.prove

  _<*>_ :  Delay (A → B) → Delay A → Delay B
  Prf goals₁ prove₁ <*> Prf goals₂ prove₂
    = Prf (goals₁ ++ goals₂ )
          λ hl → prove₁ (takeH hl) (prove₂ (dropH hl))
    where
      takeH : ∀{xs ys} → HList (xs ++ ys) → HList xs
      takeH {[]} l = []
      takeH {x ∷ xs} (x₁ ∷ l) = x₁ ∷ takeH {xs} l

      dropH : ∀{xs ys} → HList (xs ++ ys) → HList ys
      dropH {[]} l = l
      dropH {x ∷ xs} (x₁ ∷ l) = dropH {xs} l

  pure : X → Delay X
  pure x = Prf [] (const x)

  _<$>_ : (A → B) → Delay A → Delay B
  f <$> x = pure f <*> x

  later : ∀{X} → Delay X
  later {X} = Prf (X ∷ []) λ { (x ∷ []) → x }
