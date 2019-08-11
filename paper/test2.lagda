\documentclass{article}


\usepackage{agdagremlins}

\begin{document}
\begin{code}
module test2 where

open import Data.Product


module DeferredMonad where
  open import Function
  import Level
  variable ℓ ℓ₁ ℓ₂ : Level.Level
  variable A B X : Set ℓ

  record Deferred (X : Set ℓ) : Set (Level.suc ℓ) where
     constructor Prf
     field
       goals : Set
       prove : goals → X

  open Deferred
  _<*>_ :  Deferred (A → B) → Deferred A → Deferred B
  d₁ <*> d₂ = Prf (goals d₁ × goals d₂)
                λ { (p₁ , p₂ ) → prove d₁ p₁ (prove d₂ p₂) }

  join : Deferred (Deferred A) → Deferred A
  join d = Prf (Σ (goals d) (goals ∘ prove d))
            λ { (g , g′) →  prove (prove d g) g′ }

module DeferredApplicative where
  open import Data.List hiding ([_])
  open import Function

  infixr 5 _∷_
  data HList : List Set → Set where
    [] : HList []
    _∷_ : ∀{S}{SS} → S → HList SS → HList (S ∷ SS)

  import Level
  variable ℓ ℓ₁ ℓ₂ : Level.Level
  variable A B X : Set ℓ
  
  record Deferred (X : Set ℓ) : Set (Level.suc ℓ) where
     constructor Prf
     field
       goals : List Set
       prove : HList goals → X

  structure:_proofs:_done = Deferred.prove

  takeH : ∀{xs ys} → HList (xs ++ ys) → HList xs
  takeH {[]} l = []
  takeH {x ∷ xs} (x₁ ∷ l) = x₁ ∷ takeH {xs} l

  dropH : ∀{xs ys} → HList (xs ++ ys) → HList ys
  dropH {[]} l = l
  dropH {x ∷ xs} (x₁ ∷ l) = dropH {xs} l


  _<*>_ :  Deferred (A → B) → Deferred A → Deferred B
  Prf goals₁ prove₁ <*> Prf goals₂ prove₂
    = Prf (goals₁ ++ goals₂ )
          λ hl → prove₁ (takeH hl) (prove₂ (dropH hl))

  pure : X → Deferred X
  pure x = Prf [] (const x)

  _<$>_ : (A → B) → Deferred A → Deferred B
  f <$> x = pure f <*> x

  later : ∀{X} → Deferred X
  later {X} = Prf (X ∷ []) λ { (x ∷ []) → x }


-- Defer the Details when Deriving Programs
module Lang(State : Set) where
  
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



module Semantics(State : Set) where
  open Lang State
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
 





module OrderedStructures where
  open import Data.Nat

  open DeferredApplicative
  variable m n : ℕ

  data BST (m n : ℕ) : Set where
    Leaf : (m ≤ n) → BST m n
    Branch  : (x : ℕ) → BST m x → BST x n → BST m n


  branch : (x : ℕ) → Deferred (BST m x) → Deferred (BST x n)
         → Deferred (BST m n)
  branch x l r = ⦇ (Branch x) l r ⦈

  leaf : Deferred (BST m n)
  leaf = ⦇ Leaf later ⦈

  ugly : BST 2 3
  ugly = Branch 3
          (Branch 2
             (Leaf (s≤s (s≤s z≤n)))
             (Leaf (s≤s (s≤s z≤n))))
          (Leaf (s≤s (s≤s (s≤s z≤n))))

  example₂ : BST 2 10
  example₂ = structure: branch 3
                         (branch 2 leaf leaf)
                         (branch 5
                            (branch 4 leaf leaf)
                            (branch 10 leaf leaf))
             proofs:
             (s≤s (s≤s z≤n)) ∷ ((s≤s (s≤s z≤n)) ∷ ((s≤s (s≤s (s≤s z≤n))) ∷ ((s≤s (s≤s (s≤s (s≤s z≤n)))) ∷ ((s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) ∷ ((s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))) ∷ [])))))
             done

  ex : BST 2 10
  ex = Branch 3 (Branch 2 (Leaf (s≤s (s≤s z≤n))) (Leaf (s≤s (s≤s z≤n))) )
      (Branch 5 (Branch 4 (Leaf (s≤s (s≤s (s≤s z≤n)))) (Leaf (s≤s (s≤s (s≤s (s≤s z≤n))))))
      (Branch 10 (Leaf (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
      (Leaf (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))


  data OList (m n : ℕ) : Set where
    Nil  : (m ≤ n) → OList m n
    Cons : (x : ℕ) → (m ≤ x) → OList x n → OList m n

  nil : Deferred (OList m n)
  nil = ⦇ Nil later ⦈

  infixr 7 _cons_
  _cons_ : (x : ℕ) → Deferred (OList x n) → Deferred (OList m n)
  x cons xs = ⦇ (Cons x) later xs ⦈

  ls : OList 1 5
  ls = Cons 1 (s≤s z≤n)
        (Cons 2 (s≤s z≤n)
          (Cons 3 (s≤s (s≤s z≤n))
            (Cons 4 (s≤s (s≤s (s≤s z≤n)))
              (Cons 5 (s≤s (s≤s (s≤s (s≤s z≤n))))
                (Nil (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))

  example₁ : OList 1 5
  example₁ = structure: 1 cons 2 cons 3 cons 4 cons 5 cons nil
             proofs:
               s≤s z≤n
             ∷ s≤s z≤n
             ∷ s≤s (s≤s z≤n)
             ∷ s≤s (s≤s (s≤s z≤n))
             ∷ s≤s (s≤s (s≤s (s≤s z≤n)))
             ∷ s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
             ∷ []
             done


module PLang (Σ : Set) where
  open Lang Σ public
  open DeferredApplicative
  open import Function
  open import Relation.Nullary


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



  _﹕_ : Deferred [ ϕ , α ]
      → Deferred [ α , ψ ]
      → Deferred [ ϕ , ψ ]
  P ﹕ Q = ⦇ SEQ P Q ⦈

  if_then_else_fi : (g : Assertion)
                  → Deferred [ ϕ × g , ψ ]
                  → Deferred [ ϕ × ¬ g , ψ ]
                  → Deferred [ ϕ , ψ ]
  if g then p else q fi = ⦇ (IFTHENELSE g) p q ⦈

  while_begin_end : (g : Assertion)
                  → Deferred [ g × ϕ , ϕ ]
                  → Deferred [ ϕ , ¬ g × ϕ ]
  while g begin P end = ⦇ (WHILE g) P ⦈
  
  assert : (ϕ : Assertion) → Deferred [ ϕ , ψ ]
  assert ϕ = ⦇ CONS later ⦈


  guard : (g : Assertion) → Deferred [ (g → ϕ) , ϕ ]
  guard g = pure (GUARD g)

  infixr 5 _﹕_

  upd : (Σ: ϕ → Σ: ψ) → Deferred [ ϕ , ψ ]
  upd u = pure (UPD u)


module ReflectionStuff(State : Set) where
   open PLang State
   open import Reflection hiding (set)
   open import Data.Unit
   open DeferredApplicative
   open import Data.List hiding (_++_; [_])
   open import Data.String
   open import Function
   import Level
   open import Data.Nat
   open import Data.Nat.Show
   open import Data.String.Unsafe
   open import Relation.Nullary
   open import Data.Bool
   open import Data.Char hiding (_==_)
   open import Category.Applicative
   setFld : Name → TC Name
   setFld fld = bindTC (getType fld)
       λ where (pi (arg _ (def n [])) (abs _ Fld)) → do
                  bindTC (getDefinition n) 
                   λ where (record′ cn flds ) → do
                              nm ← freshName "setter"
                              Fld′ ← unquoteTC {A = Set} (Fld)
                              ty ← quoteTC {A = Set} (Fld′ → State → State)
                              declareDef (arg (arg-info visible relevant) nm) ty
                              let as-is =  (Data.List.map (getter (var 0 [])) flds)
                                  foo   = lam visible (abs "e" (lam visible (abs "σ" (con cn (replace as-is (find fld flds) (arg (arg-info visible relevant) (var 1 [])))))))
                              defineFun nm (clause [] foo ∷ [])
                              return nm
                           _ → typeError (strErr "Type is not a record type" ∷ termErr (def n []) ∷ [])
               _ → typeError (strErr "Doesn't look like a field accessor" ∷ termErr (def fld []) ∷ [])
     where
       unpack : ∀{A : Set} → Arg A → A
       unpack (arg _ a) = a
       getter : Term → Arg Name → Arg Term 
       getter t (arg _ n) = arg (arg-info visible relevant) (def n (arg (arg-info visible relevant) t ∷ []))
       process : List Char → List Char → List Char
       process a [] = a
       process a (x ∷ xs) = if not (isAlpha x) then process [] xs else process (x ∷ a) xs
       find : Name → List (Arg Name) → ℕ 
       find n [] = 0
       find n (arg _ n′ ∷ xs) with fromList (process [] (toList (showName n))) == fromList (process [] (toList (showName n′))) 
       ... | true = zero 
       ... | false = suc (find n xs)
       replace : ∀{A : Set} → List A → ℕ → A → List A
       replace [] n a = []
       replace (x ∷ xs) zero a = a ∷ xs
       replace (x ∷ xs) (suc n) a = x ∷ (replace xs n a)

   fieldSetter : ∀{X : Set} → Name → TC (X → State → State)
   fieldSetter {X} fld = do 
     setter ← setFld fld 
     unquoteTC {A = X → State → State} (def setter [])

   guarded : {ϕ ψ α : Assertion}{X : Set}
             (e : ⦃ σ : State ⦄ → ( pre : α ⦃ σ ⦄) → X)
             (set : X → State → State)
           → Deferred (Π: (ϕ → α))
           → Deferred (Π: λ ⦃ σ ⦄ → ϕ → (g : α)
                                  → ψ ⦃ set (e g) σ ⦄)
           → Deferred [ ϕ , ψ ]
   guarded e set p₁ p₂ = ⦇ update p₁ p₂ ⦈
     where update = λ ϕ→α ϕ→α→ψ → UPD λ where
             (σ , ϕ) → let
                  α = ϕ→α ⦃ σ ⦄ ϕ
                  ψ = ϕ→α→ψ ⦃ σ ⦄ ϕ α
               in set (e ⦃ σ ⦄ α) σ , ψ


   macro
    guardedM : {ϕ ψ : Assertion}{X : Set}(α : Assertion)
               (e : ⦃ σ : State ⦄ → α ⦃ σ ⦄ → X)
             → Name
             → Term → TC ⊤
    guardedM {ϕ}{ψ} α e fld hole = do
        setter ← fieldSetter fld
        trm ← quoteTC (guarded {ϕ}{ψ} e setter later later)
        unify hole trm

    syntax guardedM τ (λ g → v) fld = fld ≔′ v given g ∶ τ


   assn : {ϕ : Assertion}{X : Set}
          (e : ⦃ σ : State ⦄ → X)
          (set : X → State → State)
        → Deferred [ (λ ⦃ σ ⦄ → ϕ ⦃ set e σ ⦄)
                   , (λ ⦃ σ ⦄ → ϕ ⦃ σ ⦄) ]
   assn e set = upd λ { (σ , p) → (set (e ⦃ σ ⦄) σ , p) }

   macro 
    assnM : {ϕ : Assertion}{X : Set}
            (e : ⦃ σ : State ⦄ → X)
          → Name
          → Term → TC ⊤
    assnM {ϕ} e fld hole = do
        setter ← fieldSetter fld
        trm ← quoteTC (assn {ϕ} e setter)
        unify hole trm
    syntax assnM b a = a ≔ b

module Swap where
  open import Data.Nat

  open import Data.Unit hiding (_≤_)
  
  record SwapState : Set where
    field 
      i : ℕ 
      j : ℕ 
      temp : ℕ 

  open ReflectionStuff SwapState
  open PLang SwapState
  open DeferredApplicative
  open import Function hiding (_⟨_⟩_)
  open import Category.Applicative
  open SwapState ⦃ ... ⦄
  open import Relation.Binary.PropositionalEquality hiding ([_])

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
 
module Example where
  open import Data.Nat
  open import Data.List hiding ([_])
  
  open import Category.Applicative
  
  open import Data.Unit hiding (_≤_)
  open import Data.Empty
  open import Function hiding (_⟨_⟩_)
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open ≡-Reasoning
  open import Relation.Nullary
  open import Category.Applicative
  
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
 
  open ReflectionStuff State
  open PLang State
  open DeferredApplicative
  open State ⦃ ... ⦄ 

  lsum : [ ⊤ , result ≡ sum arr ]
  lsum = SEQ (UPD (λ { ( σ , p ) → ( record σ { i = 0 ; result = 0 } , refl , z≤n)}))
            (SEQ (WHILE  {result ≡ sum (take i arr) × i ≤ length arr} (i < length arr)
                   (UPD λ { ( σ , x , r≡sumᵢ , i≤n) →
                     ( record σ { result = result ⦃ σ ⦄ + (arr ⦃ σ ⦄ ! x) ; i = suc (i ⦃ σ ⦄) }
                     , trans (cong (_+ _) r≡sumᵢ) (take-i-plus-next x) , x ) }))
                   (CONS λ { (¬i<len , r≡sumᵢ , i≤len) →
                     trans r≡sumᵢ (trans (cong (λ h → sum (take h arr))
                                         (not-<-but-≤ ¬i<len i≤len))
                                  (cong sum (take-length {ℓ = arr}))) }))

  postulate _!!_ : List A → ℕ → A
  nope : [ ⊤ , ⊤ ]
  nope =
       structure:
         assert ⊤ ﹕
         i ≔ 0 ﹕
         result ≔ i ﹕
         while (i < length arr) begin
           assert _ ﹕
           result ≔ (result + (arr !! i)) ﹕
           i ≔ (1 + i)
         end ﹕
         assert _
       proofs:
          id ∷ (proj₂ ∷ proj₂ ∷ [])
       done

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

module BinSearch where
  open import Data.Nat
  open import Data.List hiding ([_])
  open import Data.Maybe
  open import Category.Applicative
  open import Data.Nat.Properties

  open import Data.Unit hiding (_≤_; total)
  open import Data.Empty
  open import Function hiding (_⟨_⟩_)
  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Relation.Nullary
  open import Category.Applicative
  import Function.Reasoning

  
  record State : Set where
    field
      i : ℕ
      total : ℕ
      arr : List ℕ

  open ReflectionStuff State
  open PLang State
  open DeferredApplicative
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
\end{code}
