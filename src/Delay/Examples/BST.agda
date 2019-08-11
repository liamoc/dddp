module Delay.Examples.BST where

  open import Delay
  open import Data.Nat
  variable m n : ℕ


  data BST (m n : ℕ) : Set where
    Leaf : (m ≤ n) → BST m n
    Branch  : (x : ℕ) → BST m x → BST x n → BST m n


  branch : (x : ℕ) → Delay (BST m x) → Delay (BST x n)
         → Delay (BST m n)
  branch x l r = ⦇ (Branch x) l r ⦈

  leaf : Delay (BST m n)
  leaf = ⦇ Leaf later ⦈

  ugly : BST 2 3
  ugly = Branch 3
          (Branch 2
             (Leaf (s≤s (s≤s z≤n)))
             (Leaf (s≤s (s≤s z≤n))))
          (Leaf (s≤s (s≤s (s≤s z≤n))))

  uglier : BST 2 10
  uglier = Branch 3 (Branch 2 (Leaf (s≤s (s≤s z≤n))) (Leaf (s≤s (s≤s z≤n))) )
          (Branch 5 (Branch 4 (Leaf (s≤s (s≤s (s≤s z≤n)))) (Leaf (s≤s (s≤s (s≤s (s≤s z≤n))))))
          (Branch 10 (Leaf (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
          (Leaf (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))

  better : BST 2 10
  better = structure: branch 3
                        (branch 2 leaf leaf)
                        (branch 5
                           (branch 4 leaf leaf)
                           (branch 10 leaf leaf))
           proofs:
             (s≤s (s≤s z≤n))
           ∷ (s≤s (s≤s z≤n))
           ∷ (s≤s (s≤s (s≤s z≤n)))
           ∷ (s≤s (s≤s (s≤s (s≤s z≤n))))
           ∷ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
           ∷ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))
           ∷ []
           done
