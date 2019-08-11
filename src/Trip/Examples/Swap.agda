module Trip.Examples.Swap where
  open import Data.Nat
  open import Data.Product
  open import Relation.Binary.PropositionalEquality hiding ([_])

  record SwapState : Set where
    field
      i : ℕ
      j : ℕ
      temp : ℕ
  open import Trip SwapState
  open SwapState ⦃ ... ⦄

  example′ : ∀{I J : ℕ} → [ i ≡ I × j ≡ J , j ≡ I × i ≡ J ]
  example′ = structure:
                upd (λ { (σ , p) → record σ { temp = i    ⦃ σ ⦄ } , p }) ﹕
                upd (λ { (σ , p) → record σ { i    = j    ⦃ σ ⦄ } , p }) ﹕
                upd (λ { (σ , p) → record σ { j    = temp ⦃ σ ⦄ } , p })
             proofs: []
             done

  example : ∀{I J : ℕ} → [ i ≡ I × j ≡ J , j ≡ I × i ≡ J ]
  example = structure:
                temp ≔ i ﹕ i ≔ j ﹕ j ≔ temp
            proofs: []
            done
