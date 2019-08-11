module Trip.Macros(State : Set) where
   open import Trip.Core State
   open import Trip.Surface State
   open import Delay

   open import Data.Product
   open import Reflection hiding (set)
   open import Data.Unit
   open import Data.List hiding (_++_; [_])
   open import Data.String
   open import Function
   open import Data.Nat
   open import Data.Nat.Show
   open import Data.String.Unsafe
   open import Relation.Nullary
   open import Data.Bool
   open import Data.Char hiding (_==_)
   import Level

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
           → Delay (Π: (ϕ → α))
           → Delay (Π: λ ⦃ σ ⦄ → ϕ → (g : α)
                               → ψ ⦃ set (e g) σ ⦄)
           → Delay [ ϕ , ψ ]
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
        → Delay [ (λ ⦃ σ ⦄ → ϕ ⦃ set e σ ⦄)
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
