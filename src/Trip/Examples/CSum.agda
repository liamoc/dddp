module Trip.Examples.CSum where
  open import Data.Nat
  open import Data.List hiding ([_])
  open import Data.Maybe
  open import Data.Product
  open import Data.Nat.Properties

  open import Data.Unit hiding (_≤_; total)
  open import Data.Empty
  open import Function hiding (_⟨_⟩_)
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Nullary


  record State : Set where
    field
      i : ℕ
      total : ℕ
      arr : List ℕ

  open import Trip State
  open State ⦃ ... ⦄




  _!_ : ∀ {n} → (ls : List A) → n < length ls → A
  _!_ {n = suc _} (x ∷ ls) (s≤s n) = ls ! n
  _!_ {n = zero } (x ∷ ls) (s≤s n) = x


  data _[_]=_ {A : Set} : List A → ℕ → A → Set where
    here  : ∀{x}{xs} → (x ∷ xs) [ zero ]= x
    there : ∀{x y}{xs}{n} → xs [ n ]= y → (x ∷ xs) [ suc n ]= y

  _[_]≡_ : {A : Set} → List A → ℕ → A → Set
  xs [ n ]≡ v = Σ (n < length xs) λ n<len → (xs ! n<len) ≡ v


  take-i-plus-next : ∀{i}{arr : List ℕ} → (b : i < length arr) → sum (take i arr) + arr ! b ≡ sum (take (1 + i) arr)
  take-i-plus-next {_}{[]} ()
  take-i-plus-next {zero} {x ∷ xs} (s≤s p) = sym (+-identityʳ _)
  take-i-plus-next {suc i₁} {x ∷ xs} (s≤s p) = trans (+-assoc x _ _) (cong (x +_) (take-i-plus-next p))


  drop-eq-ith-eq : ∀{i}{arr₁ arr₂ : List ℕ} (i<len₁ : i < length arr₁)(i<len₂ : i < length arr₂)
                 → drop i arr₁ ≡ drop i arr₂
                 → arr₁ ! i<len₁ ≡ arr₂ ! i<len₂
  drop-eq-ith-eq {zero} {arr₁} {arr₂} i<len₁ i<len₂ refl = cong (arr₁ !_) (≤-irrelevant i<len₁ i<len₂)
  drop-eq-ith-eq {suc i} {x₁ ∷ arr₁} {x₂ ∷ arr₂} (s≤s i<len₁) (s≤s i<len₂) dr = drop-eq-ith-eq {i}{arr₁}{arr₂} i<len₁ i<len₂ dr


  _[_]≔_ : (xs : List A){n : ℕ} → (n < length xs) → A → List A
  _[_]≔_ (x ∷ xs) {zero} n<len a = a ∷ xs
  _[_]≔_ (x ∷ xs) {suc n} (s≤s n<len) a = x ∷ (xs [ n<len ]≔ a)

  length-preserved : {A : Set}(xs : List A){n : ℕ}{a : A} → (n<len : n < length xs) → length (xs [ n<len ]≔ a) ≡ length xs
  length-preserved (x ∷ xs) {zero} n<len = refl
  length-preserved (x ∷ xs) {suc n} (s≤s n<len) = cong suc (length-preserved xs n<len)
  update-dropped : {A : Set}(xs : List A){n : ℕ}{a : A} → (n<len : n < length xs) → drop (suc n) (xs [ n<len ]≔ a) ≡ drop (suc n) xs
  update-dropped [] {zero} ()
  update-dropped [] {suc n} ()
  update-dropped (x ∷ xs) {zero} (s≤s n<len) = refl
  update-dropped (x ∷ xs) {suc n} (s≤s n<len) = update-dropped xs n<len

  drop-empty : ∀{A : Set}{a : List A}{n : ℕ} → drop n a ≡ [] → drop (suc n) a ≡ []
  drop-empty {A} {a} {zero} refl = refl
  drop-empty {A} {[]} {suc n} p = refl
  drop-empty {A} {x ∷ a} {suc n} p = drop-empty {A}{a}{n} p

  drop-suc : ∀{A : Set}{a b : List A}{n : ℕ} → drop n a ≡ drop n b → drop (suc n) a ≡ drop (suc n ) b
  drop-suc {A} {x ∷ xs} {_} {zero} refl = refl
  drop-suc {A} {x ∷ xs} {[]} {suc n} p = drop-empty {A}{xs}{n} p
  drop-suc {A} {x ∷ xs} {y ∷ ys} {suc n} p = drop-suc {A}{xs}{ys}{n} p
  drop-suc {A} {[]} {_} {zero} refl = refl
  drop-suc {A} {[]} {x ∷ xs} {suc n} p = sym (drop-empty {A}{xs}{n} (sym p))
  drop-suc {A} {[]} {[]} {suc n} p = refl

  open import Relation.Binary.Core using (Tri)
  less-suc : ∀{j i}{P : Set} → (j < suc i) → (j < i → P) → (j ≡ i → P) → P
  less-suc {j}{i} j<si lp ep with <-cmp j i
  ... | Tri.tri< a ¬b ¬c = lp a
  ... | Tri.tri≈ ¬a b ¬c = ep b
  ... | Tri.tri> ¬a ¬b c = ⊥-elim (<⇒≱ j<si c)

  unrelated-update : ∀{X : Set}{arr : List X}{i j}{u n}(i<len : i < length arr)
                   → j ≢ i
                   → arr [ j ]= n
                   → (arr [ i<len ]≔ u) [ j ]= n
  unrelated-update {i = zero} p ne here = ⊥-elim (ne refl)
  unrelated-update {i = suc i} (s≤s p) ne here = here
  unrelated-update {i = zero} (s≤s p) ne (there f) = there f
  unrelated-update {i = suc i} (s≤s p) ne (there f) = there (unrelated-update p (λ n≡i → ne (cong suc n≡i)) f )

  related-update : ∀{X : Set}{arr : List X}{i}{n}(i<len : i < length arr)
                 → (arr [ i<len ]≔ n) [ i ]= n
  related-update {X} {x ∷ arr₁} {zero} (s≤s p) = here
  related-update {X} {x ∷ arr₁} {suc i} (s≤s p) = there (related-update {X}{arr₁}{i} p)

  example : ∀{arr₀}
          → [ arr ≡ arr₀ × length arr > 0
            , length arr ≡ length arr₀
            × (∀ i → (i < length arr) → arr [ i ]= sum (take (suc i) arr₀) )
            ]
  example {arr₀} = let
       Inv : ℕ → ℕ → Assertion
       Inv i i′ ⦃ σ ⦄ = (length arr ≡ length arr₀)
                      × (i ≤ length arr)
                      × (∀ j (j<i : j < i) → arr [ j ]= sum (take (suc j) arr₀))
                      ×  drop i arr ≡ drop i arr₀
                      × total ≡ sum (take i′ arr₀)
    in structure:
       assert (arr ≡ arr₀ × length arr > 0) ﹕
       i ≔ 0 ﹕
       total ≔ 0 ﹕
       assert (i ≡ 0 × total ≡ 0 × arr ≡ arr₀ × i < length arr) ﹕
       while (i < length arr) begin
         total ≔′ total + (arr ! i<len) given i<len ∶ (i < length arr) ﹕
         assert ( (i < length arr) ×  Inv i (suc i)) ﹕
         arr ≔′ (arr [ i<len ]≔ total) given i<len ∶ (i < length arr) ﹕
         assert (Inv (suc i) (suc i)) ﹕
         i ≔ (1 + i)
       end ﹕
       assert (¬ (i < length arr) × Inv i i )
       proofs:
         (λ pre → refl , refl , pre)
       ∷ (λ { (i≡0 , total≡0 , arr≡arr₀ , i<len)
            → (let open ≡-Reasoning
                in begin length arr  ≡⟨ cong length arr≡arr₀ ⟩
                         length arr₀ ∎)
            , (let open ≤-Reasoning
                in begin i          ≤⟨ n≤1+n i ⟩
                         suc i      ≤⟨ i<len   ⟩
                         length arr ∎)
            , (λ j j<i → let open Function.Reasoning
                          in j<i               ∶ j < i
                          |> subst (j <_) i≡0  ∶ j < 0
                          |> m<n⇒n≢0           ∶ 0 ≢ 0
                          |> (_$ refl)         ∶ ⊥
                          |> ⊥-elim            )
            , (let open ≡-Reasoning
                in begin drop i arr        ≡⟨ cong (drop i) arr≡arr₀ ⟩
                         drop i arr₀       ∎)
            , (let open ≡-Reasoning
                in begin total             ≡⟨ total≡0 ⟩
                         0                 ≡⟨ refl ⟩
                         sum []            ≡⟨ refl ⟩
                         sum (take 0 arr₀) ≡⟨ cong (λ i → sum (take i _)) (sym i≡0) ⟩
                         sum (take i arr₀) ∎)
            })
       ∷ (λ { ( i<len , invariant ) → i<len })
       ∷ (λ { ( _ , len≡len₀ , i≤len , accum , drops , takes ) i<len
            → i<len , len≡len₀ , i≤len , accum , drops
            , let open ≡-Reasoning
                  i<len₀ : i < length arr₀
                  i<len₀ = subst (i <_) len≡len₀ i<len
               in begin total + (arr  ! i<len )             ≡⟨ cong (total +_) (drop-eq-ith-eq i<len i<len₀ drops) ⟩
                        total + (arr₀ ! i<len₀)             ≡⟨ cong (_+ _) takes ⟩
                        sum (take i arr₀) + (arr₀ ! i<len₀) ≡⟨ take-i-plus-next i<len₀ ⟩
                        sum (take (suc i) arr₀)             ∎ })
       ∷ (λ { ( i<len , invariant ) → i<len , invariant })
       ∷ (λ { ( i<len , invariant ) → i<len } )
       ∷ (λ { ( _ , len≡len₀ , i≤len , accum , drops , takes ) i<len
            → (let open ≡-Reasoning
                in begin length (arr [ i<len  ]≔ total) ≡⟨ length-preserved arr i<len ⟩
                         length arr                     ≡⟨ len≡len₀ ⟩
                         length arr₀ ∎)
            , (let open ≤-Reasoning
                in begin suc i                           ≤⟨ i<len ⟩
                         length arr                      ≡⟨ sym (length-preserved arr i<len) ⟩
                         length (arr [ i<len ]≔ total )  ∎)
            , (λ j j<si → less-suc j<si
                (λ j<i → let open Function.Reasoning
                          in accum j j<i                      ∶ ( arr                   [ j ]= sum (take (suc j) arr₀))
                          |> unrelated-update i<len (<⇒≢ j<i) ∶ ((arr [ i<len ]≔ total) [ j ]= sum (take (suc j) arr₀)))

                (λ j≡i → let open ≡-Reasoning
                          in subst id (begin
                               (arr [ i<len ]≔ total) [ i ]= total                   ≡⟨ cong (_ [_]= _) (sym j≡i) ⟩
                               (arr [ i<len ]≔ total) [ j ]= total                   ≡⟨ cong (_ [ j ]=_) takes ⟩
                               (arr [ i<len ]≔ total) [ j ]= sum (take (suc i) arr₀) ≡⟨ cong (λ x → _ [ j ]= sum (take (suc x) arr₀)) (sym j≡i) ⟩
                               (arr [ i<len ]≔ total) [ j ]= sum (take (suc j) arr₀) ∎)
                             (related-update i<len))
              )
            , (let open ≡-Reasoning
                in begin drop (suc i) (arr [ i<len ]≔ total) ≡⟨ update-dropped arr i<len ⟩
                         drop (suc i) arr                    ≡⟨ drop-suc {_}{arr}{arr₀} drops ⟩
                         drop (suc i) arr₀ ∎)
            , takes
            })
       ∷ (λ { inv → inv })
       ∷ (λ { ( i≮len , len≡len₀ , i≤len , accum , drops , takes ) → len≡len₀
            , λ j j<len → let open Function.Reasoning
                              len≡i = sym (≤-antisym i≤len (≮⇒≥ i≮len))
                           in j<len              ∶ j < length arr
                           |> subst (j <_) len≡i ∶ j < i
                           |> accum j            ∶ (arr [ j ]= sum (take (suc j) arr₀))
            })
       ∷ []
       done
   where import Function.Reasoning
