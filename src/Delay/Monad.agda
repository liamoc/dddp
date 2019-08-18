module Delay.Monad where
  open import Function
  import Level
  open import Data.Unit
  open import Data.Product

  variable ℓ ℓ₁ ℓ₂ : Level.Level
  variable A B X : Set ℓ

  data Tuple : Set₁
  ⟦_⟧ : Tuple → Set

  data Tuple where
    `Set : Set → Tuple
    `Σ   : (A : Tuple) (B : ⟦ A ⟧ → Tuple) → Tuple

  ⟦ `Set A ⟧ = A
  ⟦ `Σ A B ⟧ = Σ[ a ∈ ⟦ A ⟧ ] ⟦ B a ⟧

  linearise-k : (t : Tuple) (k : ⟦ t ⟧ → Tuple) → Tuple
  linearise-k (`Set A) k = `Σ (`Set A) k
  linearise-k (`Σ A B) k = linearise-k A λ a →
                           linearise-k (B a) λ b →
                           k (a , b)

  linearise : (t : Tuple) → Tuple
  linearise t = linearise-k t λ _ → `Set ⊤

  sound-k : ∀ t {k} → ⟦ linearise-k t k ⟧ → Σ[ v ∈ ⟦ t ⟧ ] ⟦ k v ⟧
  sound-k (`Set A) p = p
  sound-k (`Σ A B) p =
    let (a , p')  = sound-k A     p  in
    let (b , p'') = sound-k (B a) p' in
    (a , b) , p''

  sound : ∀ t → ⟦ linearise t ⟧ → ⟦ t ⟧
  sound t p = let (v , _) = sound-k t p in v

  _`×_ : (A B : Tuple) → Tuple
  A `× B = `Σ A (λ _ → B)

  record MDelay (X : Set ℓ) : Set (Level.suc ℓ) where
     constructor Prf
     field
       goals    : Tuple
       oldprove : ⟦ goals ⟧ → X

     prove : ⟦ linearise goals ⟧ → X
     prove = oldprove ∘ sound goals

  open MDelay
  _<*>_ :  MDelay (A → B) → MDelay A → MDelay B
  d₁ <*> d₂ = Prf (goals d₁ `× goals d₂)
                λ { (p₁ , p₂ ) → oldprove d₁ p₁ (oldprove d₂ p₂) }

  pure : X → MDelay X
  pure x = Prf (`Set ⊤) (const x)

  join : MDelay (MDelay A) → MDelay A
  join d = Prf (`Σ (goals d) (goals ∘ oldprove d))
            λ { (g , g′) →  oldprove (oldprove d g) g′ }
