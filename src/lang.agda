module lang where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True ; toWitness)


-- TODO(FIX): Clean up these infix operators
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

-- infixr 7 _⇒_
-- infixr 7 𝕋_⇒_
infixr 7 _𝕋⇒_

infix  5 ƛ_
-- infix  5 μ_
-- infix  5 Y_
infixl 7 _·_
-- infix  8 `suc_
-- infix  9 `_
infix  9 S_
infix  200 #_
infix  2 _—→_


data Ty : Set where
  𝕋𝕟   : Ty
  𝕋𝕓   : Ty
  _𝕋⇒_ : Ty → Ty → Ty

data Ctx : Set where
  ∅   : Ctx
  _,_ : Ctx → Ty → Ctx


-- proof that Context contains an element of that type
data _∋_ : Ctx → Ty → Set where
  Z : ∀ {Γ A}
    → Γ , A ∋ A
  S_ : ∀ {Γ A B}
    → Γ ∋ A
    → Γ , B ∋ A

-- the resulting type of evaluating a context
data _⊢_ : Ctx → Ty → Set where
  Term_ : ∀ {Γ A}
    → Γ ∋ A
    → Γ ⊢ A

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
    → Γ ⊢ A 𝕋⇒ B 

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A 𝕋⇒ B
    → Γ ⊢ A
    → Γ ⊢ B

  num : ∀ {Γ}
    → ℕ
    → Γ ⊢ 𝕋𝕟

  _⊹_ : ∀ {Γ}
    → Γ ⊢ 𝕋𝕟
    → Γ ⊢ 𝕋𝕟
    → Γ ⊢ 𝕋𝕟

  _★_ : ∀ {Γ}
    → Γ ⊢ 𝕋𝕟
    → Γ ⊢ 𝕋𝕟
    → Γ ⊢ 𝕋𝕟
  -- -- JumpNotZero, the `case` in PLFA
  -- jnz_¿_⟪_∥_⟫ : ∀ {Γ A}
  --   → Γ ⊢ 𝕋𝕟
  --   → Γ ⊢ A
  --   → Γ , 𝕋𝕟 ⊢ A
  --   → Γ ⊢ A
 
  true : ∀ {Γ}
    → Γ ⊢ 𝕋𝕓

  false : ∀ {Γ}
    → Γ ⊢ 𝕋𝕓

  ¿_⦅_∥_⦆ : ∀ {Γ A}
    → Γ ⊢ 𝕋𝕓 -- condition
    → Γ ⊢ A -- if True
    → Γ ⊢ A -- if False
    → Γ ⊢ A

  -- -- fixpoint Y combinator
  -- Y_ : ∀ {Γ A}
  --   → Γ , A ⊢ A
  --   → Γ ⊢ A

data Val : ∀ {Γ A} → Γ ⊢ A → Set where
  𝕍𝕟     : ∀ {Γ n}
    → Val (num {Γ} n)
  𝕍true  : ∀ {Γ}
    → Val (true  {Γ})
  𝕍false : ∀ {Γ}
    → Val (false {Γ})
  𝕍clos  : ∀ {Γ A B} → {N : Γ , A ⊢ B}
    → Val (ƛ N)

{- Helper functions
-}

length : Ctx → ℕ
length ∅         = zero
length ( Γ , _ ) = suc (length Γ)

lookup : {Γ : Ctx} → {n : ℕ} → (p : n < length Γ) → Ty
lookup {(_ , A)} {zero}    (s≤s z≤n) = A
lookup {(Γ , _)} {(suc n)} (s≤s p)   = lookup p

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {_ , _} {zero}    (s≤s z≤n) = Z
count {Γ , _} {(suc n)} (s≤s p)   = S (count p)

{- get the Term `n` declerations back -}
#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ} = Term count (toWitness n∈Γ)

{- example programs -}

two : ∀ {Γ} → Γ ⊢ 𝕋𝕟
two = num 2 

twoTimesTwo : ∀ {Γ} → Γ ⊢ 𝕋𝕟
twoTimesTwo = two ★ two

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
rename ρ true            = true
rename ρ false           = false
rename ρ (ƛ N)           = ƛ (rename (ext ρ) N)
rename ρ (¿ L ⦅ M ∥ N ⦆) = ¿ (rename ρ L) ⦅ (rename ρ M) ∥ (rename ρ N) ⦆
rename ρ (num M)         = num M
rename ρ (Term x)        = Term (ρ x)
rename ρ (L ★ M)         = (rename ρ L) ★ (rename ρ M)
rename ρ (L ⊹ M)         = (rename ρ L) ⊹ (rename ρ M)
rename ρ (L · M)         = (rename ρ L) · (rename ρ M)
-- rename ρ (μ N)          =  μ (rename (ext ρ) N)

exts : ∀ {Γ Δ}
  → (∀ {A}   →     Γ ∋ A →     Δ ⊢ A)
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  Term Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ true             = true
subst σ false            = false
subst σ (ƛ N)            = ƛ (subst (exts σ) N)
subst σ (¿ L ⦅ M ∥ N ⦆ ) = ¿ (subst σ L) ⦅ (subst σ M) ∥ (subst σ N) ⦆
subst σ (num M)          = (num M)
subst σ (Term x)         = σ x
subst σ (L ★ M)          = (subst σ L) ★ (subst σ M)
subst σ (L ⊹ M)          = (subst σ L) ⊹ (subst σ M)
subst σ (L · M)          = (subst σ L) · (subst σ M)
-- subst σ (μ N)          =  μ (subst (exts σ) N)

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
  σ (S x)  =  Term x


{- Reductions
 ξ : compatibility, reduce a part of a term
 β : eliminate a constructor combined with a destructor
 δ : apply a built in bifunctor
-}
data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  -- function is reduced to closure value
  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A 𝕋⇒ B} {M : Γ ⊢ A}
    → L —→ L′
    → L · M —→ L′ · M
  -- argument is reduced in function application
  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A 𝕋⇒ B} {M M′ : Γ ⊢ A}
    → Val V
    → M —→ M′
    → V · M —→ V · M′
  -- apply function
  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Val W
    → ((ƛ N) · W) —→ (N [ W ])
  -- simplify condition
  ξ-¿ : ∀ {Γ A} {L L′ : Γ ⊢ 𝕋𝕓} {M : Γ ⊢ A} {N : Γ ⊢ A}
    → L —→ L′
    → ¿ L ⦅ M ∥ N ⦆ —→ ¿ L′ ⦅ M ∥ N ⦆
  -- if statement on truth
  β-¿true : ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}
    → ¿ true ⦅ M ∥ N ⦆ —→ M
  -- if statement on falsity
  β-¿false : ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ A}
    → ¿ false ⦅ M ∥ N ⦆ —→ N

  ξ-⊹₁ : ∀ {Γ} {L L′ M : Γ ⊢ 𝕋𝕟}
    → L —→ L′
    → L ⊹ M —→ L′ ⊹ M
  ξ-⊹₂ : ∀ {Γ} {V L L′ : Γ ⊢ 𝕋𝕟}
    → Val V
    → L —→ L′
    → V ⊹ L —→ V ⊹ L′
  δ-⊹ : ∀ {Γ c d}
    → num {Γ} c ⊹ num d —→ num (c + d)
  ξ-★₁ : ∀ {Γ} {L L′ M : Γ ⊢ 𝕋𝕟}
    → L —→ L′
    → L ★ M —→ L′ ★ M
  ξ-★₂ : ∀ {Γ} {V L L′ : Γ ⊢ 𝕋𝕟}
    → Val V
    → L —→ L′
    → V ★ L —→ V ★ L′
  δ-★ : ∀ {Γ c d}
    → num {Γ} c ★ num d —→ num (c * d)

  -- apply fixpoint function
  -- β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
  --   → μ N —→ N [ μ N ]

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

-- Take multiple reduction steps
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


data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
    → Progress M

  done :
      Val M
    → Progress M

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (Term ())
progress (ƛ N)                          =  done 𝕍clos
progress (L · M) with progress L
...    | step L—→L′                     =  step (ξ-·₁ L—→L′)
...    | done 𝕍clos with progress M
...        | step M—→M′                 =  step (ξ-·₂ 𝕍clos M—→M′)
...        | done VM                    =  step (β-ƛ VM)
progress (num n)                        =  done 𝕍𝕟
progress (L ⊹ M) with progress L
...    | step L—→L′                     =  step (ξ-⊹₁ L—→L′)
...    | done 𝕍𝕟 with progress M
...        | step M—→M′                 =  step (ξ-⊹₂ 𝕍𝕟 M—→M′)
...        | done 𝕍𝕟                    =  step (δ-⊹)
progress (L ★ M) with progress L
...    | step L—→L′                     =  step (ξ-★₁ L—→L′)
...    | done 𝕍𝕟 with progress M
...        | step M—→M′                 =  step (ξ-★₂ 𝕍𝕟 M—→M′)
...        | done 𝕍𝕟                    =  step (δ-★)
progress (true) = done 𝕍true
progress (false) = done 𝕍false
progress (¿ C ⦅ T ∥ F ⦆ ) with progress C
...    | step C—→C′                     = step (ξ-¿ C—→C′)
...    | done 𝕍true                     = step (β-¿true)
...    | done 𝕍false                    = step (β-¿false)
-- progress (`suc M) with progress M
-- ...    | step M—→M′                     =  step (ξ-suc M—→M′)
-- ...    | done VM                        =  done (V-suc VM)
-- progress (case L M N) with progress L
-- ...    | step L—→L′                     =  step (ξ-case L—→L′)
-- ...    | done V-zero                    =  step (β-zero)
-- ...    | done (V-suc VL)                =  step (β-suc VL)
-- progress (μ N)                          =  step (β-μ)

record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished {Γ A} (N : Γ ⊢ A) : Set where
   done :
       Val N
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
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin



plus : ∅ ⊢ 𝕋𝕟 𝕋⇒ 𝕋𝕟 𝕋⇒ 𝕋𝕟
plus = ƛ (ƛ ( ( # 1 ) ⊹  # 0 ))

2+2=4 : plus · two · two —↠ ( num 4 )
2+2=4 = begin
  ((ƛ (ƛ ((Term (S Z)) ⊹ (Term Z)))) · num 2 · num 2 —→⟨
    ξ-·₁ (β-ƛ 𝕍𝕟) ⟩
    (ƛ (num 2 ⊹ (Term Z))) · num 2 —→⟨ β-ƛ 𝕍𝕟 ⟩
    (num 2 ⊹ num 2) —→⟨ δ-⊹ ⟩ num 4 ∎)
