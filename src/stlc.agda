module stlc where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True ; toWitness)

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_

{- Definition of language
-}

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
    → Γ , A ∋ A
  S_ : ∀ {Γ A B}
    → Γ ∋ A
    → Γ , B ∋ A

data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢ A

  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
    → Γ ⊢ B

  `zero : ∀ {Γ}
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
    → Γ ⊢ A

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
    → Γ ⊢ A


{- Helper functions
-}

length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
lookup {(Γ , _)} {(suc n)} (s≤s p)    =  lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero}    (s≤s z≤n)  =  Z
count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ}  =  ` count (toWitness n∈Γ)

{- Example programs
-}

two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0)
    (`suc (# 3 · # 0 · # 1)
  ))

mul : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
mul = μ ƛ ƛ (case (# 1) (`zero)
    (plus · (# 1) · (# 3 · # 0 · # 1))
  )

2+2 : ∀ {Γ} → Γ ⊢ `ℕ
2+2 = plus · two · two

-- { mul · two · two }
-- { eval (gas 100) ( mul · (two) · (two) ) }

{- renaming
-}

-- Extension lemma
ext : ∀ {Γ Δ}
  → (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
rename ρ (`suc M)       =  `suc (rename ρ M)
rename ρ (case L M N)   =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ N)          =  μ (rename (ext ρ) N)

exts : ∀ {Γ Δ}
  → (∀ {A}   →     Γ ∋ A →     Δ ⊢ A)
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` x)          =  σ x
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ (`zero)        =  `zero
subst σ (`suc M)       =  `suc (subst σ M)
subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N)          =  μ (subst (exts σ) N)

-- Substitution
-- substitutes the innermost free variable with the given term
_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z      =  M
  σ (S x)  =  ` x


{- Values
-}

data Value : ∀ {Γ A} → Γ ⊢ A → Set where
  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
    → Value (ƛ N)
  V-zero : ∀ {Γ}
    → Value (`zero {Γ})
  V-suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
    → Value (`suc V)

infix 2 _—→_

{- Reductions
 ξ : compatibility, reduce a part of a term
 β : simplify a constructor combined with a destructor
-}
data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  -- function in application is reduced
  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
    → L · M —→ L′ · M
  -- value in application is reduced
  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
    → V · M —→ V · M′
  -- substitute value in function
  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
    → (ƛ N) · W —→ N [ W ]
  -- recurse inside suc
  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
    → `suc M —→ `suc M′
  -- recurse case on input
  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
    → case L M N —→ case L′ M N
  -- case switch on zero
  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → case `zero M N —→ M
  -- case switch on suc
  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
    → case (`suc V) M N —→ N [ V ]
  -- apply fixpoint function
  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
    → μ N —→ N [ μ N ]


infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where
  _∎ : (M : Γ ⊢ A)
    → M —↠ M
  _—→⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
  → M —↠ N
begin M—↠N = M—↠N


{- Example reductions
-}

2+2=4 : plus {∅} · two · two —↠ `suc `suc `suc `suc `zero
2+2=4 = begin
    plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z))) · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ case two (` Z) (`suc (plus · ` Z · ` S Z))) · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two two (`suc (plus · ` Z · two))
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z)))
      · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ case (`suc `zero) (` Z) (`suc (plus · ` Z · ` S Z))) · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (case (`suc `zero) (two) (`suc (plus · ` Z · two)))
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc (`suc (plus · `zero · two))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc (`suc ((ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z)))
      · `zero · two))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc (`suc ((ƛ case `zero (` Z) (`suc (plus · ` Z · ` S Z))) · two))
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc (`suc (case `zero (two) (`suc (plus · ` Z · two))))
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎



data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
    → Progress M

  done :
      Value M
    → Progress M

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ N)                          =  done V-ƛ
progress (L · M) with progress L
...    | step L—→L′                     =  step (ξ-·₁ L—→L′)
...    | done V-ƛ with progress M
...        | step M—→M′                 =  step (ξ-·₂ V-ƛ M—→M′)
...        | done VM                    =  step (β-ƛ VM)
progress (`zero)                        =  done V-zero
progress (`suc M) with progress M
...    | step M—→M′                     =  step (ξ-suc M—→M′)
...    | done VM                        =  done (V-suc VM)
progress (case L M N) with progress L
...    | step L—→L′                     =  step (ξ-case L—→L′)
...    | done V-zero                    =  step (β-zero)
...    | done (V-suc VL)                =  step (β-suc VL)
progress (μ N)                          =  step (β-μ)

record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished {Γ A} (N : Γ ⊢ A) : Set where

   done :
       Value N
     → Finished N

   out-of-gas :
       Finished N

data Steps {A} : ∅ ⊢ A → Set where

  steps : {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
    → Steps L

eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin

sucμ : ∅ ⊢ `ℕ
sucμ = μ (`suc (# 0))

_ : eval (gas 4) sucμ ≡
  steps
   (μ `suc ` Z
   —→⟨ β-μ ⟩
    `suc (μ `suc ` Z)
   —→⟨ ξ-suc β-μ ⟩
    `suc (`suc (μ `suc ` Z))
   —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc (`suc (`suc (μ `suc ` Z)))
   —→⟨ ξ-suc (ξ-suc (ξ-suc β-μ)) ⟩
    `suc (`suc (`suc (`suc (μ `suc ` Z))))
   ∎)
   out-of-gas
_ = refl

