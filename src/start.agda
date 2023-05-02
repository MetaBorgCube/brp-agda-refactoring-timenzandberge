module start where

open import Agda.Builtin.Nat public
open import Relation.Nullary public
open import Data.Empty public
open import Data.Unit public


data Calc : Set where
  num : Nat → Calc
  add : Calc → Calc → Calc
  mul : Calc → Calc → Calc
  _≱_ : Calc → Calc → Calc
  if_then_else_ : Calc → Calc → Calc → Calc
  true : Calc
  false : Calc
  ⌐ : Calc → Calc
  _∧_ : Calc → Calc → Calc
  _∨_ : Calc → Calc → Calc


data Val : Set where
  numV : Nat → Val
  trueV : Val
  falseV : Val

data Ty : Set where
  number : Ty
  boolean : Ty

data WtCalc : Calc → Ty → Set where
  □num : ∀ { n } → WtCalc (num n) number
  □add : ∀ {e1 e2}
    → WtCalc e1 (number)
    → WtCalc e2 (number)
    → ( WtCalc ((add e1 e2) ) (number))
  □mul : ∀ {e1 e2}
    → WtCalc e1 number
    → WtCalc e2 number
    → WtCalc (mul e1 e2) number
  □true : WtCalc (true) boolean
  □false : WtCalc (false) boolean
  □≱ : ∀ {e1 e2}
    → WtCalc e1 number
    → WtCalc e2 number
    → WtCalc (e1 ≱ e2) boolean
  □ite : ∀ {cond e1 e2 type}
    → WtCalc cond boolean
    → WtCalc e1 type
    → WtCalc e2 type
    → WtCalc (if cond then e1 else e2) type
  □⌐ : ∀ {b}
    → WtCalc b boolean
    → WtCalc (⌐ b) boolean
  □∧ : ∀ {b1 b2}
    → WtCalc b1 boolean
    → WtCalc b2 boolean
    → WtCalc (b1 ∧ b2) boolean
  □∨ : ∀ {b1 b2}
    → WtCalc b1 boolean
    → WtCalc b2 boolean
    → WtCalc (b1 ∨ b2) boolean


_lessThan_ : Nat → Nat → Val
zero lessThan zero = falseV
zero lessThan suc y = trueV
suc x lessThan zero = falseV
suc x lessThan suc y = x lessThan y

data _↓_ : Calc → Val → Set where
  ↓num : ∀ { n } → (num n) ↓ (numV n)
  ↓add : ∀ {e1 e2}
    → ∀ {v1} → e1 ↓ (numV v1)
    → ∀ {v2} → e2 ↓ (numV v2)
    → ( _↓_ ((add e1 e2) ) (numV (v1 + v2)))
  ↓mul : ∀ {e1 e2}
    → ∀ {v1} → e1 ↓ (numV v1)
    → ∀ {v2} → e2 ↓ (numV v2)
    → ( _↓_ (mul e1 e2) (numV (v1 * v2)))
  ↓true : (true) ↓ (trueV)
  ↓false : (false) ↓ (falseV)
  ↓≱ : ∀ {e1 e2}
    → ∀ {v1} → e1 ↓ (numV v1)
    → ∀ {v2} → e2 ↓ (numV v2)
    → ( _↓_ (e1 ≱ e2) ((v1 lessThan v2)) )
  ↓itetrue : ∀ {cond e1 e2}
    → ∀ {v1} → e1 ↓ (v1)
    -- → ∀ {v2} → e2 ↓ (v2)
    → cond ↓ (trueV)
    → ( _↓_ (if cond then e1 else e2) ( v1 ) )
  ↓itefalse : ∀ {cond e1 e2}
    -- → ∀ {v1} → e1 ↓ (v1)
    → ∀ {v2} → e2 ↓ (v2)
    → cond ↓ (falseV)
    → ( _↓_ (if cond then e1 else e2) ( v2 ) )
  ↓notTrue : ∀ {e1}
    → e1 ↓ (trueV)
    → ( ( ⌐ e1 ) ↓ (falseV) )
  ↓notFalse : ∀ {e1}
    → e1 ↓ (falseV)
    → ( ( ⌐ e1 ) ↓ (trueV) )
  ↓andTrue : ∀ {e1 e2}
    → e1 ↓ (trueV)
    → e2 ↓ (trueV)
    → ( ( e1 ∧ e2 ) ↓ (trueV) )
  ↓andFalseFirst : ∀ {e1 e2}
    → e1 ↓ (trueV)
    → e2 ↓ (falseV)
    → ( ( e1 ∧ e2 ) ↓ (falseV) )
  ↓andFalseSecond : ∀ {e1 e2}
    → e1 ↓ (falseV)
    → e2 ↓ (trueV)
    → ( ( e1 ∧ e2 ) ↓ (falseV) )
  ↓andFalseBoth : ∀ {e1 e2}
    → e1 ↓ (falseV)
    → e2 ↓ (falseV)
    → ( ( e1 ∧ e2 ) ↓ (falseV) )
  ↓orTrue : ∀ {e1 e2}
    → e1 ↓ (trueV)
    → e2 ↓ (trueV)
    → ( ( e1 ∨ e2 ) ↓ (trueV) )
  ↓orFalseFirst : ∀ {e1 e2}
    → e1 ↓ (falseV)
    → e2 ↓ (trueV)
    → ( ( e1 ∨ e2 ) ↓ (trueV) )
  ↓orFalseSecond : ∀ {e1 e2}
    → e1 ↓ (trueV)
    → e2 ↓ (falseV)
    → ( ( e1 ∨ e2 ) ↓ (trueV) )
  ↓orFalseBoth : ∀ {e1 e2}
    → e1 ↓ (falseV)
    → e2 ↓ (falseV)
    → ( ( e1 ∨ e2 ) ↓ (falseV) )


infixr 15 _↓_

v1 : Val
v1 = numV 5

ex1 : Calc
ex1 = num 5

↓ex1 : ex1 ↓ v1
↓ex1 = ↓num

ty1 : WtCalc ex1 number
ty1 = □num

v2 : Val
v2 = numV 14

ex2 : Calc
ex2 = add ( num 6 ) ( num 8 )

↓ex2 : ex2 ↓ v2
↓ex2 = ↓add ↓num ↓num

ty2 : WtCalc ex2 number
ty2 = □add □num □num

v3 : Val
v3 = numV 18

ex3 : Calc
ex3 = mul (num 2) (add (num 8) (num 1))

↓ex3 : ex3 ↓ v3
↓ex3 = ↓mul ↓num (↓add ↓num ↓num)

ty3 : WtCalc ex3 number
ty3 = □mul □num (□add □num □num)

v4 : Val
v4 = trueV

ex4 : Calc
ex4 = (num 5) ≱ (num 9)

↓ex4 : ex4 ↓ v4
↓ex4 = ↓≱ ↓num ↓num

ty4 : WtCalc ex4 boolean
ty4 = □≱ □num □num

v5 : Val
v5 = numV 20

ex5 : Calc
ex5 = if (true ∧ false) then ( add (num 5)  (num 9)) else (mul (num 5)  (num 4))

↓ex5 : ex5 ↓ v5
↓ex5 = ↓itefalse (↓mul ↓num ↓num) (↓andFalseFirst ↓true ↓false)

ty5 : WtCalc ex5 number
ty5 = □ite (□∧ □true □false) (□add □num □num) (□mul □num □num)

v6 : Val
v6 = trueV

ex6 : Calc
ex6 = false ∨ true

↓ex6 : ex6 ↓ v6
↓ex6 = ↓orFalseFirst ↓false ↓true

ty6 : WtCalc ex6 boolean
ty6 = □∨ □false □true

v7 : Val
v7 = trueV

ex7 : Calc
ex7 = ⌐ (false ∧ true)

↓ex7 : ex7 ↓ v7
↓ex7 = ↓notFalse (↓andFalseSecond ↓false ↓true)

ty7 : WtCalc ex7 boolean
ty7 = □⌐ (□∧ □false □true)

exEmpty : Calc
exEmpty = (num 5) ≱ (false)

↓exEmpty : ∀ {v} → ¬ (exEmpty ↓ v)
↓exEmpty (↓≱ ↓num ())

exEmpty2 : Calc
exEmpty2 = ⌐ (num 8)

↓exEmpty2 : ∀ {v} → ¬ (exEmpty2 ↓ v)
↓exEmpty2 (↓notTrue ())
↓exEmpty2 (↓notFalse ())


exDoubleNeg : Calc
exDoubleNeg = ⌐ ( ⌐ false )

vDoubleNeg : Val
vDoubleNeg = falseV

↓DoubleNeg : exDoubleNeg ↓ vDoubleNeg
↓DoubleNeg = ↓notTrue (↓notFalse ↓false)

tyDoubeNeg : WtCalc exDoubleNeg boolean
tyDoubeNeg = □⌐ (□⌐ □false)


dne : Calc → Calc
dne (num x) = num x
dne (add c g) = add (dne c) (dne g)
dne (mul c g) = mul (dne c) (dne g)
dne (c ≱ g) = ((dne c) ≱ (dne g))
dne (if c then one else two) = if dne c then dne one else dne two
dne true = true
dne false = false
dne (⌐ (⌐ c)) = dne c
dne (⌐ (num x)) = ⌐ (num x)
dne (⌐ (add c g)) = ⌐ ( add (dne c) (dne g) )
dne (⌐ (mul c g)) = ⌐ ( mul (dne c) (dne g) )
dne (⌐ (c ≱ g)) = ⌐ (dne c ≱ dne g)
dne (⌐ (if c then e1 else e2)) = ⌐ (if (dne c) then (dne e1) else (dne e2))
dne (⌐ true)  = ⌐ true
dne (⌐ false) = ⌐ false
dne (⌐ (c ∧ g)) = ⌐ ((dne c) ∧ (dne g))
dne (⌐ (c ∨ g)) = ⌐ ((dne c) ∨ (dne g))
dne (c ∧ g) = dne c ∧ dne g
dne (c ∨ g) = dne c ∨ dne g

sameType : (c : Calc) → (t : Ty) → ( WtCalc c t ) → (WtCalc (dne c) t)
sameType (num x) number □num = □num
sameType (num x) boolean ()
sameType (add c c₁) number (□add p p₁) = □add (sameType c number p) (sameType c₁ number p₁)
sameType (add c c₁) boolean ()
sameType (mul c c₁) number (□mul p p₁) = □mul (sameType c number p) (sameType c₁ number p₁)
sameType (mul c c₁) boolean ()
sameType (c ≱ c₁) number ()
sameType (c ≱ c₁) boolean (□≱ p p₁) = □≱ (sameType c number p) (sameType c₁ number p₁)
sameType (if c then c₁ else c₂) number (□ite p p₁ p₂) = □ite (sameType c boolean p) (sameType c₁ number p₁) (sameType c₂ number p₂)
sameType (if c then c₁ else c₂) boolean (□ite p p₁ p₂) = □ite (sameType c boolean p) (sameType c₁ boolean p₁) (sameType c₂ boolean p₂)
sameType true number ()
sameType true boolean □true = □true
sameType false number ()
sameType false boolean □false = □false
sameType (⌐ c) number ()
sameType (⌐ (c ≱ c₁)) boolean (□⌐ p) = □⌐ (sameType (c ≱ c₁) boolean p)
sameType (⌐ (if c then c₁ else c₂)) boolean (□⌐ p) = □⌐ (sameType (if c then c₁ else c₂) boolean p)
sameType (⌐ true) boolean (□⌐ p) = □⌐ p
sameType (⌐ false) boolean (□⌐ p) = □⌐ p
sameType (⌐ (c ∧ c₁)) boolean (□⌐ p) = □⌐ (sameType (c ∧ c₁) boolean p)
sameType (⌐ (c ∨ c₁)) boolean (□⌐ p) = □⌐ (sameType (c ∨ c₁) boolean p)
sameType (c ∧ c₁) number ()
sameType (c ∧ c₁) boolean (□∧ p p₁) = □∧ (sameType c boolean p) (sameType c₁ boolean p₁)
sameType (c ∨ c₁) number ()
sameType (c ∨ c₁) boolean (□∨ p p₁) = □∨ (sameType c boolean p) (sameType c₁ boolean p₁) 
sameType (⌐ (⌐ c)) boolean (□⌐ (□⌐ p)) = sameType c boolean p


sameValue :  { c : Calc } →  {v : Val} → (c ↓ v) → ((dne c) ↓ v)
sameValue ↓num = ↓num
sameValue (↓add p p₁) = ↓add (sameValue p) (sameValue p₁)
sameValue (↓mul p p₁) = ↓mul (sameValue p) (sameValue p₁)
sameValue ↓true = ↓true
sameValue ↓false = ↓false
sameValue (↓≱ p p₁) = ↓≱ (sameValue p) (sameValue p₁)
sameValue (↓itetrue p p₁) = ↓itetrue (sameValue p) (sameValue p₁)
sameValue (↓itefalse p p₁) = ↓itefalse (sameValue p) (sameValue p₁)
sameValue (↓andTrue p p₁) = ↓andTrue (sameValue p) (sameValue p₁)
sameValue (↓andFalseFirst p p₁) = ↓andFalseFirst (sameValue p) (sameValue p₁)
sameValue (↓andFalseSecond p p₁) = ↓andFalseSecond (sameValue p) (sameValue p₁)
sameValue (↓andFalseBoth p p₁) = ↓andFalseBoth (sameValue p) (sameValue p₁)
sameValue (↓orTrue p p₁) = ↓orTrue (sameValue p) (sameValue p₁)
sameValue (↓orFalseFirst p p₁) = ↓orFalseFirst (sameValue p) (sameValue p₁)
sameValue (↓orFalseSecond p p₁) = ↓orFalseSecond (sameValue p) (sameValue p₁)
sameValue (↓orFalseBoth p p₁) = ↓orFalseBoth (sameValue p) (sameValue p₁)
sameValue {⌐ (e1 ≱ e2)} {.falseV} (↓notTrue p) = ↓notTrue (sameValue p)
sameValue {⌐ true} {.falseV} (↓notTrue p) = ↓notTrue p
sameValue {⌐ (e1 ∧ e2)} {.falseV} (↓notTrue p) = ↓notTrue (sameValue p)
sameValue {⌐ (e1 ∨ e2)} (↓notTrue p) = ↓notTrue (sameValue p)
sameValue {⌐ (if e1 then e2 else e3)} {.falseV} (↓notTrue p) = ↓notTrue (sameValue p)
sameValue {⌐ (⌐ e1)}  (↓notTrue (↓notFalse p)) = sameValue p
sameValue {⌐ (e1 ≱ e2)} (↓notFalse p) = ↓notFalse (sameValue p)
sameValue {⌐ (if e1 then e2 else e3)} (↓notFalse p) = ↓notFalse (sameValue p)
sameValue {⌐ false} (↓notFalse p) = ↓notFalse p
sameValue {⌐ (⌐ e1)} (↓notFalse (↓notTrue p)) = sameValue p
sameValue {⌐ (e1 ∧ e2)} (↓notFalse p) = ↓notFalse (sameValue p)
sameValue {⌐ (e1 ∨ e2)} (↓notFalse p) = ↓notFalse (sameValue p)


data hasNoDoubleNeg : Calc → Set where
  noNnum : ∀ {n} → hasNoDoubleNeg ( num n )
  noNadd : ∀ {e1 e2}
    → hasNoDoubleNeg e1
    → hasNoDoubleNeg e2
    → hasNoDoubleNeg (add e1 e2)
  noNmul : ∀ {e1 e2}
    → hasNoDoubleNeg e1
    → hasNoDoubleNeg e2
    → hasNoDoubleNeg (mul e1 e2)
  noN≱ : ∀ {e1 e2}
    → hasNoDoubleNeg e1
    → hasNoDoubleNeg e2
    → hasNoDoubleNeg (e1 ≱ e2)
  noNif_nothen_noelse_ : ∀ {cond e1 e2}
    → hasNoDoubleNeg cond
    → hasNoDoubleNeg e1
    → hasNoDoubleNeg e2
    → hasNoDoubleNeg (if cond then e1 else e2)
  noNtrue : hasNoDoubleNeg true
  noNfalse : hasNoDoubleNeg false
  noN∧ : ∀ {e1 e2}
    → hasNoDoubleNeg e1
    → hasNoDoubleNeg e2
    → hasNoDoubleNeg (e1 ∧ e2)
  noN∨ : ∀ {e1 e2}
    → hasNoDoubleNeg e1
    → hasNoDoubleNeg e2
    → hasNoDoubleNeg (e1 ∨ e2)
  oonoNnum : ∀ {n} → hasNoDoubleNeg ( ⌐ ( num n ))
  oonoNadd : ∀ {e1 e2}
    → hasNoDoubleNeg e1
    → hasNoDoubleNeg e2
    → hasNoDoubleNeg ( ⌐ (add e1 e2))
  oonoNmul : ∀ {e1 e2}
    → hasNoDoubleNeg e1
    → hasNoDoubleNeg e2
    → hasNoDoubleNeg ( ⌐ (mul e1 e2))
  oonoN≱ : ∀ {e1 e2}
    → hasNoDoubleNeg e1
    → hasNoDoubleNeg e2
    → hasNoDoubleNeg ( ⌐ (e1 ≱ e2))
  oonoNif_nothen_noelse_ : ∀ {cond e1 e2}
    → hasNoDoubleNeg cond
    → hasNoDoubleNeg e1
    → hasNoDoubleNeg e2
    → hasNoDoubleNeg ( ⌐ (if cond then e1 else e2))
  oonoNtrue : hasNoDoubleNeg (⌐ true)
  oonoNfalse : hasNoDoubleNeg (⌐ false)
  oonoN∧ : ∀ {e1 e2}
    → hasNoDoubleNeg e1
    → hasNoDoubleNeg e2
    → hasNoDoubleNeg ( ⌐ (e1 ∧ e2))
  oonoN∨ : ∀ {e1 e2}
    → hasNoDoubleNeg e1
    → hasNoDoubleNeg e2
    → hasNoDoubleNeg ( ⌐ (e1 ∨ e2))

dneNoDoubleNeg : ( c : Calc ) → hasNoDoubleNeg (dne c)
dneNoDoubleNeg (num x) = noNnum
dneNoDoubleNeg (add x x₁) = noNadd (dneNoDoubleNeg x) (dneNoDoubleNeg x₁)
dneNoDoubleNeg (mul x x₁) = noNmul (dneNoDoubleNeg x) (dneNoDoubleNeg x₁)
dneNoDoubleNeg (x ≱ x₁) = noN≱ (dneNoDoubleNeg x) (dneNoDoubleNeg x₁)
dneNoDoubleNeg (if x then x₁ else x₂) = noNif dneNoDoubleNeg x nothen dneNoDoubleNeg x₁ noelse dneNoDoubleNeg x₂
dneNoDoubleNeg true = noNtrue
dneNoDoubleNeg false = noNfalse
dneNoDoubleNeg (⌐ (num x)) = oonoNnum
dneNoDoubleNeg (⌐ (add x x₁)) = oonoNadd (dneNoDoubleNeg x) (dneNoDoubleNeg x₁)
dneNoDoubleNeg (⌐ (mul x x₁)) = oonoNmul (dneNoDoubleNeg x) (dneNoDoubleNeg x₁)
dneNoDoubleNeg (⌐ (x ≱ x₁)) = oonoN≱ (dneNoDoubleNeg x) (dneNoDoubleNeg x₁)
dneNoDoubleNeg (⌐ (if x then x₁ else x₂)) = oonoNif dneNoDoubleNeg x nothen dneNoDoubleNeg x₁ noelse dneNoDoubleNeg x₂
dneNoDoubleNeg (⌐ true) = oonoNtrue
dneNoDoubleNeg (⌐ false) = oonoNfalse
-- dneNoDoubleNeg (⌐ (⌐ x)) = dneNoDoubleNeg x
dneNoDoubleNeg (⌐ (x ∧ x₁)) = oonoN∧ (dneNoDoubleNeg x) (dneNoDoubleNeg x₁)
dneNoDoubleNeg (⌐ (x ∨ x₁)) = oonoN∨ (dneNoDoubleNeg x) (dneNoDoubleNeg x₁)
dneNoDoubleNeg (x ∧ x₁) = noN∧ (dneNoDoubleNeg x) (dneNoDoubleNeg x₁)
dneNoDoubleNeg (x ∨ x₁) = noN∨ (dneNoDoubleNeg x) (dneNoDoubleNeg x₁)


