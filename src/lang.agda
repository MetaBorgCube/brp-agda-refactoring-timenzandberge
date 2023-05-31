module lang where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app) public
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Empty using (⊥ ; ⊥-elim) public
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤?_; z≤n; s≤s) public
open import Data.Maybe renaming (_>>=_ to bind) public
open import Relation.Nullary using (¬_) public
open import Relation.Nullary.Decidable using (True ; toWitness) public


-- TODO(FIX): Clean up these infix operators
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

-- infixr 7 _⇒_
-- infixr 7 𝕋_⇒_
infixr 7 _𝕋⇒_

infix  5 ƛ_
infix  4 _>>=_
-- infix  5 μ_
-- infix  5 Y_
infixl 7 _·_
-- infix  8 `suc_
-- infix  9 `_
infix  9 S_
infix  100 num
infix  200 #_
infix  2 _—→_


data Ty : Set where
  𝕋𝕟     : Ty
  𝕋𝕓     : Ty
  _𝕋⇒_   : Ty → Ty → Ty
  𝕋maybe : Ty

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

  Nothing : ∀ {Γ}
    → Γ ⊢ 𝕋maybe

  Just : ∀ {Γ}
    → Γ ⊢ 𝕋𝕟
    → Γ ⊢ 𝕋maybe
  
  _>>=_ : ∀ {Γ}
    → Γ ⊢ 𝕋maybe
    → Γ ⊢ 𝕋𝕟 𝕋⇒ 𝕋maybe
    → Γ ⊢ 𝕋maybe

  do<-_⁀_ : ∀ {Γ}
    → Γ ⊢ 𝕋maybe
    → Γ , 𝕋𝕟 ⊢ 𝕋maybe
    → Γ ⊢ 𝕋maybe

  -- -- fixpoint Y combinator
  -- Y_ : ∀ {Γ A}
  --   → Γ , A ⊢ A
  --   → Γ ⊢ A
-- return = Just

data Val : ∀ {Γ A} → Γ ⊢ A → Set where
  𝕍𝕟       : ∀ {Γ n}
    → Val (num {Γ} n)
  𝕍true    : ∀ {Γ}
    → Val (true  {Γ})
  𝕍false   : ∀ {Γ}
    → Val (false {Γ})
  𝕍clos    : ∀ {Γ A B} → {N : Γ , A ⊢ B}
    → Val (ƛ N)
  𝕍nothing : ∀ {Γ}
    → Val (Nothing {Γ})
  -- 𝕍just    : ∀ {Γ A} → {N : Γ , A ⊢ 𝕋𝕟}
  --   → Val (Just N)
  𝕍just    : ∀ {Γ n}
    → Val (Just {Γ} (num n))

data Value : Set where
  num𝕍 : ℕ → Value
  true𝕍 : Value
  false𝕍 : Value
  clos𝕍 : ∀ {Γ A B} → (Γ , A ⊢ B) → Value
  nothing𝕍 : Value
  just𝕍 : ℕ → Value
  

{- Helper functions
-}
private
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

private
  two : ∀ {Γ} → Γ ⊢ 𝕋𝕟
  two = num 2 

  twoTimesTwo : ∀ {Γ} → Γ ⊢ 𝕋𝕟
  twoTimesTwo = two ★ two

{- renaming
-}

private
  -- Extension lemma
  ext : ∀ {Γ Δ}
    → (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
    → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
  ext ρ Z      =  Z
  ext ρ (S x)  =  S (ρ x)

  rename : ∀ {Γ Δ}
    → (∀ {A} → Γ ∋ A → Δ ∋ A)
    → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
  rename ρ true              = true
  rename ρ false             = false
  rename ρ (ƛ N)             = ƛ (rename (ext ρ) N)
  rename ρ (¿ L ⦅ M ∥ N ⦆)   = ¿ (rename ρ L) ⦅ (rename ρ M) ∥ (rename ρ N) ⦆
  rename ρ (num M)           = num M
  rename ρ (Term x)          = Term (ρ x)
  rename ρ (L ★ M)           = (rename ρ L) ★ (rename ρ M)
  rename ρ (L ⊹ M)           = (rename ρ L) ⊹ (rename ρ M)
  rename ρ (L · M)           = (rename ρ L) · (rename ρ M)
  rename ρ Nothing           = Nothing
  rename ρ (Just c)          = Just (rename ρ c)
  rename ρ (f >>= m)         = (rename ρ f) >>= (rename ρ m)
  rename ρ (do<- m ⁀ f) = do<- (rename ρ m) ⁀ (rename (ext ρ) f)
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
  subst σ Nothing          = Nothing
  subst σ (Just c)         = Just (subst σ c)
  subst σ (f >>= m)        = (subst σ f) >>= (subst σ m)
  subst σ (do<- m ⁀ f) = do<- (subst σ m) ⁀ (subst (exts σ) f)
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
  -- Bind operator
  ξ->>=₁ : ∀ {Γ} {L L′ : Γ ⊢ 𝕋maybe} {M : Γ ⊢ 𝕋𝕟 𝕋⇒ 𝕋maybe}
    → L —→ L′
    → L >>= M —→ L′ >>= M
  ξ->>=₂ : ∀ {Γ} {V : Γ ⊢ 𝕋maybe } { M M′ : Γ ⊢ 𝕋𝕟 𝕋⇒ 𝕋maybe}
    → Val V
    → M —→ M′
    → V >>= M —→ V >>= M′
  β->>=Nothing : ∀ {Γ} {F : Γ ⊢ 𝕋𝕟 𝕋⇒ 𝕋maybe }
    → Nothing >>= (F ) —→ Nothing
  β->>=Just : ∀ {Γ} {F : Γ , 𝕋𝕟 ⊢ 𝕋maybe } {M : Γ ⊢ 𝕋𝕟 }
    → Val M
    → (Just M) >>= (ƛ F) —→ (F [ M ])
  -- Do notation
  ξ-do₁ : ∀ {Γ} {L L′ : Γ ⊢ 𝕋maybe} {M : Γ , 𝕋𝕟 ⊢ 𝕋maybe}
    → L —→ L′
    → do<- L ⁀ M —→ do<- L′ ⁀ M
  β-doNothing : ∀ {Γ} {F : Γ , 𝕋𝕟 ⊢ 𝕋maybe }
    → do<- Nothing ⁀ (F) —→ Nothing
  β-doJust : ∀ {Γ} {F : Γ , 𝕋𝕟 ⊢ 𝕋maybe } {M : Γ ⊢ 𝕋𝕟 }
    → Val M
    → do<- (Just M) ⁀ (F) —→ (F [ M ])
  -- Just reduction
  ξ-JustInternal : ∀ {Γ} {M M′ : Γ ⊢ 𝕋𝕟}
    → M —→ M′
    → Just M —→ Just M′

  -- apply fixpoint function
  -- β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
  --   → μ N —→ N [ μ N ]

data _↓_ : ∀ {Γ A} → (Γ ⊢ A) → Value → Set where
  ↓num : ∀ {Γ n} → _↓_ (num {Γ} n) (num𝕍 n)
  ↓add : ∀ {Γ} {el er : Γ ⊢ 𝕋𝕟}
    → ∀ {vl} → _↓_ el (num𝕍 vl)
    → ∀ {vr} → _↓_ er (num𝕍 vr)
    → _↓_ (el ⊹ er) (num𝕍 (vl + vr))
  ↓mul : ∀ {Γ} {el er : Γ ⊢ 𝕋𝕟}
    → ∀ {vl} → _↓_ el (num𝕍 vl)
    → ∀ {vr} → _↓_ er (num𝕍 vr)
    → _↓_ (el ⊹ er) (num𝕍 (vl * vr))
  ↓true : ∀ {Γ} → (true {Γ}) ↓ (true𝕍)
  ↓false : ∀ {Γ} → (false {Γ}) ↓ (false𝕍)
  ↓¿true : ∀ {Γ A} {cond : Γ ⊢ 𝕋𝕓} {e1 e2 : Γ ⊢ A}
    → cond ↓ true𝕍
    → ∀ {v1} → e1 ↓ v1
    → (¿ cond ⦅ e1 ∥ e2 ⦆) ↓ v1
  ↓¿false : ∀ {Γ A} {cond : Γ ⊢ 𝕋𝕓} {e1 e2 : Γ ⊢ A}
    → cond ↓ false𝕍
    → ∀ {v2} → e2 ↓ v2
    → (¿ cond ⦅ e1 ∥ e2 ⦆) ↓ v2
  ↓lam : ∀ {Γ} {A B : Ty} (el : Γ , A ⊢ B)
    → ( ƛ (el)) ↓ (clos𝕍 el)
  ↓app : {Γ : Ctx} {A B : Ty} {el : Γ ⊢ A 𝕋⇒ B} {input : Γ ⊢ A}
    → ∀ {body : Γ , A ⊢ B} → el ↓ (clos𝕍 body)
    → ∀ {inv} → input ↓ (inv)
    → ∀ {val} → (body [ input ] ) ↓ val
    → (el · input) ↓ val
  ↓nothing : ∀ {Γ : Ctx} → Nothing {Γ} ↓ nothing𝕍
  ↓just : ∀ {Γ : Ctx} {expr : Γ ⊢ 𝕋𝕟}
    → ∀ {n} → expr ↓ (num𝕍 n)
    → ( Just expr ) ↓ (just𝕍 n )
  ↓bindJust : ∀ {Γ} {monad : Γ ⊢ 𝕋maybe} {funct : Γ ⊢ 𝕋𝕟 𝕋⇒ 𝕋maybe}
    → ∀ {n} → monad ↓ (just𝕍 n)
    → ∀ {body : Γ , 𝕋𝕟 ⊢ 𝕋maybe} → funct ↓ (clos𝕍 body)
    → ∀ {val} → (body [ (num n) ] ) ↓ val
    → (monad >>= funct) ↓ val
  ↓bindNothing : ∀ {Γ} {monad : Γ ⊢ 𝕋maybe} {funct : Γ ⊢ 𝕋𝕟 𝕋⇒ 𝕋maybe}
    → monad ↓ nothing𝕍
    → (monad >>= funct) ↓ nothing𝕍
  ↓doJust : ∀ {Γ} {monad : Γ ⊢ 𝕋maybe} {expr : Γ , 𝕋𝕟 ⊢ 𝕋maybe}
    → ∀ {n} → monad ↓ (just𝕍 n)
    → ∀ {val} → (expr [ (num n) ] ) ↓ val
    → (do<- monad ⁀ expr) ↓ val
  ↓doNothing : ∀ {Γ} {monad : Γ ⊢ 𝕋maybe} {expr : Γ , 𝕋𝕟 ⊢ 𝕋maybe}
    → monad ↓ nothing𝕍
    → (do<- monad ⁀ expr) ↓ nothing𝕍



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
progress Nothing                        = done 𝕍nothing
progress (Just N) with progress N
...    | step x = step (ξ-JustInternal x)
...    | done 𝕍𝕟 = done 𝕍just
progress (M >>= F) with progress M
...    | step M—→M′                     = step (ξ->>=₁ M—→M′)
...    | done 𝕍nothing                  = step (β->>=Nothing )
...    | done (𝕍just) with progress F
...        | step x                     = step (ξ->>=₂ 𝕍just x)
...        | done 𝕍clos                 = step (β->>=Just 𝕍𝕟)
progress (do<- M ⁀ F) with progress M
...    | step M—→M′                     = step (ξ-do₁ M—→M′)
...    | done 𝕍nothing                  = step (β-doNothing)
...    | done (𝕍just)                   = step (β-doJust 𝕍𝕟)
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


-- stepsToValue : ∀ {A : Ty} → ∀ {L N : ∅ ⊢ A} → (L —↠ N) → (Val N) → Maybe 𝕍clos
-- stepsToValue (x) = ?


private
  {- Example programs
  -}
  plus : ∅ ⊢ 𝕋𝕟 𝕋⇒ 𝕋𝕟 𝕋⇒ 𝕋𝕟
  plus = ƛ (ƛ ( ( # 1 ) ⊹  # 0 ))

  2+2=4 : plus · two · two —↠ ( num 4 )
  2+2=4 = begin
    ((ƛ (ƛ ((Term (S Z)) ⊹ (Term Z)))) · num 2 · num 2 —→⟨
      ξ-·₁ (β-ƛ 𝕍𝕟) ⟩
      (ƛ (num 2 ⊹ (Term Z))) · num 2 —→⟨ β-ƛ 𝕍𝕟 ⟩
      (num 2 ⊹ num 2) —→⟨ δ-⊹ ⟩ num 4 ∎)


  -- monadplusone : ∅ ⊢ 𝕋𝕟 𝕋⇒ 𝕋maybe
  -- monadplusone = ƛ ( Just ( (num 1) ⊹ # 0 ))

  bindEx : ∅ ⊢ 𝕋maybe
  bindEx = (Just (num 1)) >>= ƛ (Just (num 1 ⊹ # 0 )) 

  doEx : ∅ ⊢ 𝕋maybe
  doEx =
    do<- Just (num 1) ⁀
    Just ((num 1) ⊹ # 0)

  doChain : ∅ ⊢ 𝕋maybe
  doChain =
    do<- Just (num 1) ⁀
    do<- Just (num 1) ⁀
    Just ( # 1 ⊹ # 0)


  evalbindex : bindEx —↠ (Just (num 2))
  evalbindex =
    (Just (num 1) >>= ƛ Just (num 1 ⊹ (Term Z)) —→⟨ β->>=Just 𝕍𝕟 ⟩
      Just (num 1 ⊹ num 1) —→⟨ ξ-JustInternal δ-⊹ ⟩ Just (num 2) ∎)

  bigstepbindex : bindEx ↓ (just𝕍 2)
  bigstepbindex = ↓bindJust (↓just ↓num) (↓lam (Just (num 1 ⊹ (Term Z)))) (↓just (↓add ↓num ↓num))

  evaldoex : doEx —↠ (Just (num 2))
  evaldoex =
    ((do<- Just (num 1) ⁀ Just (num 1 ⊹ (Term Z))) —→⟨ β-doJust 𝕍𝕟 ⟩
      Just (num 1 ⊹ num 1) —→⟨ ξ-JustInternal δ-⊹ ⟩ Just (num 2) ∎)

  bigstepdoex : doEx ↓ (just𝕍 2)
  bigstepdoex = ↓doJust (↓just ↓num) (↓just (↓add ↓num ↓num))
