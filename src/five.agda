module five where

open import Agda.Builtin.Nat


data Calc : Set where
  num : Nat → Calc
  add : Calc → Calc → Calc
  mul : Calc → Calc → Calc
  _≱_ : Calc → Calc → Calc
  if_then_else_ : Calc → Calc → Calc → Calc
  true : Calc
  false : Calc
  ¬ : Calc → Calc
  _∧_ : Calc → Calc → Calc
  _∨_ : Calc → Calc → Calc

data Val : Set where
  numV : Nat → Val

data _↓_ : Calc → Val → Set where
  ↓num : ∀ { n } → (num n) ↓ (numV n)
  ↓add : ∀ {e1 e2}
    → ∀ {v1} → e1 ↓ (numV v1)
    → ∀ {v2} → e2 ↓ (numV v2)
    → ( _↓_ ((add e1 e2) ) (numV (v1 + v2)))
  ↓mul : ∀ {e1 e2}
    → ∀ {v1} → e1 ↓ (numV v1)
    → ∀ {v2} → e2 ↓ (numV v2)
    → ( _↓_ ((mul e1 e2) ) (numV (v1 * v2)))
  ↓≱ : ∀ {e1 e2}
    → ∀ {v1} → e1 ↓ (numV v1)
    → ∀ {v2} → e2 ↓ (numV v2)
    → ( e1 ≱ e2 ) ↓ (? ( v1 < v2 ))


infixr 15 _↓_

ex1 : Calc
ex1 = num 5

v1 : Val
v1 = numV 5

↓ex1 : ex1 ↓ v1
↓ex1 = ↓num

ex2 : Calc
ex2 = add ( num 6 ) ( num 8 )

v2 : Val
v2 = numV 14

↓ex2 : ex2 ↓ v2
↓ex2 = ↓add ↓num ↓num

ex3 : Calc
ex3 = mul (num 2) (add (num 8) (num 1))

v3 : Val
v3 = numV 18

↓ex3 : ex3 ↓ v3
↓ex3 = ↓mul ↓num (↓add ↓num ↓num)


ex4 : Calc
ex4 = if true then (num 5) else (num 7)

v4 : Val
v4 = numV 5

↓ex4 : ex4 ↓ v4
↓ex4 = {!  !}

ex5 : Calc
ex5 = if false then (num 5) else (num 7)

v5 : Val
v5 = numV 7

ex6 : Calc
ex6 = if ( (num 6) ≱ (num 9) ) then (num 20) else (num 10)

v6 : Val
v6 = numV 20

ex7 : Calc
ex7 = if ( true ∧ false ) then (num 20) else ( if (true ∨ false) then (num 30) else (num 40))

v7 : Val
v7 = numV 30
