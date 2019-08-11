module Delay.Examples.OList where
  open import Delay
  open import Data.Nat
  variable m n : ℕ
  
  data OList (m n : ℕ) : Set where
    Nil  : (m ≤ n) → OList m n
    Cons : (x : ℕ) → (m ≤ x) → OList x n → OList m n

  nil : Delay (OList m n)
  nil = ⦇ Nil later ⦈

  infixr 7 _cons_
  _cons_ : (x : ℕ) → Delay (OList x n) → Delay (OList m n)
  x cons xs = ⦇ (Cons x) later xs ⦈

  ugly : OList 1 5
  ugly = Cons 1 (s≤s z≤n)
          (Cons 2 (s≤s z≤n)
            (Cons 3 (s≤s (s≤s z≤n))
              (Cons 4 (s≤s (s≤s (s≤s z≤n)))
                (Cons 5 (s≤s (s≤s (s≤s (s≤s z≤n))))
                  (Nil (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))

  better : OList 1 5
  better = structure: 1 cons 2 cons 3 cons 4 cons 5 cons nil
           proofs:
             s≤s z≤n
           ∷ s≤s z≤n
           ∷ s≤s (s≤s z≤n)
           ∷ s≤s (s≤s (s≤s z≤n))
           ∷ s≤s (s≤s (s≤s (s≤s z≤n)))
           ∷ s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
           ∷ []
           done
