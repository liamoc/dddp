module Trip(State : Set) where
  open import Trip.Surface(State) public
  open import Trip.Macros(State) public
  open import Trip.Core(State) using ([_,_]; Assertion) public
  open import Delay public
