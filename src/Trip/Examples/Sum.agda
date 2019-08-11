module Trip.Examples.Sum where

  open import Data.Product
  open import Data.Nat
  open import Data.List hiding ([_])
  open import Data.Unit hiding (_≤_)
  open import Data.Empty
  open import Function hiding (_⟨_⟩_)
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Nullary

  _!_ : ∀ {n : ℕ}{A : Set} → (ls : List A) → n < length ls → A
  [] ! ()
  _!_ {suc _} (x ∷ ls) (s≤s n) = ls ! n
  _!_ {zero} (x ∷ ls) (s≤s n) = x


  not-<-but-≤ : ∀{x y} → (x < y → ⊥) → x ≤ y → x ≡ y
  not-<-but-≤ {zero} {zero} a b = refl
  not-<-but-≤ {zero} {suc y} a b = ⊥-elim (a (s≤s z≤n))
  not-<-but-≤ {suc x} {zero} a ()
  not-<-but-≤ {suc x} {suc y} a (s≤s b) = cong suc (not-<-but-≤ (a ∘ s≤s) b)

  take-length : ∀{A : Set}{ℓ : List A} → take (length ℓ) ℓ ≡ ℓ
  take-length {ℓ = []} = refl
  take-length {ℓ = x ∷ ℓ} = cong (x ∷_) take-length


  n+0≡n : ∀{n} → n + 0 ≡ n
  n+0≡n {zero} = refl
  n+0≡n {suc n} = cong suc n+0≡n

  +-assoc : ∀{a b c} → (a + b) + c ≡ a + (b + c)
  +-assoc {zero} = refl
  +-assoc {suc a} = cong suc (+-assoc {a})

  take-i-plus-next : ∀{i}{arr : List ℕ} → (b : i < length arr) → sum (take i arr) + arr ! b ≡ sum (take (1 + i) arr)
  take-i-plus-next {_}{[]} ()
  take-i-plus-next {zero} {x ∷ xs} (s≤s p) = sym n+0≡n
  take-i-plus-next {suc i₁} {x ∷ xs} (s≤s p) = trans (+-assoc {x}) (cong (x +_) (take-i-plus-next p))

  record State : Set where
    field
      i : ℕ
      arr : List ℕ
      result : ℕ

  open import Trip State
  open State ⦃ ... ⦄

  ugly : [ ⊤ , result ≡ sum arr ]
  ugly = SEQ (UPD (λ { ( σ , p ) → ( record σ { i = 0 ; result = 0 } , refl , z≤n)}))
            (SEQ (WHILE  {result ≡ sum (take i arr) × i ≤ length arr} (i < length arr)
                   (UPD λ { ( σ , x , r≡sumᵢ , i≤n) →
                     ( record σ { result = result ⦃ σ ⦄ + (arr ⦃ σ ⦄ ! x) ; i = suc (i ⦃ σ ⦄) }
                     , trans (cong (_+ _) r≡sumᵢ) (take-i-plus-next x) , x ) }))
                   (CONS λ { (¬i<len , r≡sumᵢ , i≤len) →
                     trans r≡sumᵢ (trans (cong (λ h → sum (take h arr))
                                         (not-<-but-≤ ¬i<len i≤len))
                                  (cong sum (take-length {ℓ = arr}))) }))
    where open import Trip.Core State

  example : [ ⊤ , result ≡ sum arr ]
  example =
       structure:
         assert ⊤ ﹕
         i ≔ 0 ﹕
         result ≔ i ﹕
         assert (i ≡ 0 × result ≡ 0) ﹕
         while (i < length arr) begin
           result ≔′ result + (arr ! i<len) given i<len ∶ (i < length arr) ﹕
           i ≔ (1 + i)
         end ﹕
         assert (¬ i < length arr × result ≡ sum (take i arr) × i ≤ length arr )
       proofs:
           (λ x → refl , refl)
         ∷ (λ { (refl , refl) → refl , z≤n })
         ∷ (λ { (i<len , r≡sumᵢ , i≤len) → i<len })
         ∷ (λ { (_ , r≡sumᵢ , i≤len) i<len →
              ( begin result + (arr ! i<len)           ≡⟨ cong (_+ _) r≡sumᵢ ⟩
                      sum (take i arr) + (arr ! i<len) ≡⟨ take-i-plus-next i<len ⟩
                      sum (take (1 + i) arr)           ∎)
              , i<len
              } )
         ∷ (λ { (¬i<len , r≡sumᵢ , i≤len)
              → begin result                      ≡⟨ r≡sumᵢ ⟩
                      sum (take i arr)            ≡⟨ cong (λ □ → sum (take □ arr)) (not-<-but-≤ ¬i<len i≤len) ⟩
                      sum (take (length arr) arr) ≡⟨ cong sum (take-length {ℓ = arr}) ⟩
                      sum arr                     ∎
              } )
         ∷ []
       done
   where open ≡-Reasoning
