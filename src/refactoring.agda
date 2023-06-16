module refactoring where

open import lang
open import Data.Product public
open import Data.Bool hiding ( _≟_ )
-- import Agda.Builtin.Unit
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app) public
open Eq.≡-Reasoning using (begin_ ; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat
open import Data.Nat.Properties

variable ty A B : Ty
variable C : Ctx
variable v w : Value A
variable L : C ⊢ A

-- Contextual equivalence
data _≅_ : (v : Value ty) → (w : Value ty) → Set where
  num𝕍x≅num𝕍y : ∀ {x y}
    → x ≡ y
    → (num𝕍 x) ≅ (num𝕍 y)
  true𝕍≅true𝕍 : true𝕍 ≅ true𝕍
  -- true𝕍 ≅ false𝕍 : ⊥
  -- false𝕍 ≅ true𝕍 : ⊥
  false𝕍≅false𝕍 : false𝕍 ≅ false𝕍
  nothing𝕍≅nothing𝕍 : nothing𝕍 ≅ nothing𝕍
  -- nothing𝕍 ≅ just𝕍 x : ⊥
  -- just𝕍 x ≅ nothing𝕍 : ⊥
  just𝕍≅just𝕍 : {x y : ℕ} → x ≡ y → (just𝕍 x) ≅ (just𝕍 y)
  clos𝕍≅clos𝕍 : {aTy rTy : Ty} {f g : C , aTy ⊢ rTy}
    → ∀ { ArgV : Value aTy }
    → { retVf retVg : Value rTy }
    → f ↓ retVf
    → g ↓ retVg
    → retVf ≅ retVg
    → clos𝕍 f ≅ clos𝕍 g 

--   num𝕍 x ≅ num𝕍 y = x ≡ y
--   true𝕍 ≅ true𝕍 = ⊤
--   true𝕍 ≅ false𝕍 = ⊥
--   false𝕍 ≅ true𝕍 = ⊥
--   false𝕍 ≅ false𝕍 = ⊤
--   nothing𝕍 ≅ nothing𝕍 = ⊤
--   nothing𝕍 ≅ just𝕍 x = ⊥
--   just𝕍 x ≅ nothing𝕍 = ⊥
--   just𝕍 x ≅ just𝕍 y = x ≡ y
--   clos𝕍 {Γ} {aTy} {rTy} f ≅ clos𝕍 {Δ} g =
--     ∀ { ArgV : Value aTy }
--     → { retVf retVg : Value rTy }
--     → retVf ≅ retVg
--     → f ↓ retVf
--     → g ↓ retVg
--     → ⊤
--   
-- -- ClosV {argTy = argTy} {retTy} γₒ bₒ ≡ᵣ ClosV γₙ bₙ = 
-- --     ∀ {argVₒ : Value argTy} {argVₙ : Value (MaybeTy→ListTy argTy)} {argVₒ≡ᵣargV : argVₒ ≡ᵣ argVₙ} 
-- --     {retVₒ : Value retTy} {retVₙ : Value (MaybeTy→ListTy retTy)} → 
-- --     γₒ ,' argVₒ ⊢e bₒ ↓ retVₒ → 
-- --     (γₙ ,' argVₙ) ⊢e bₙ ↓ retVₙ → 
-- --     retVₒ ≡ᵣ retVₙ → 
-- --     ⊤


removeDo : C ⊢ A → C ⊢ A
removeDo (Term x) = Term x
removeDo (ƛ L) = ƛ (removeDo L)
removeDo (L · M) = (removeDo L) · (removeDo M)
removeDo (num x) = num x
removeDo (L ⊹ M) = (removeDo L) ⊹ (removeDo M)
removeDo (L ★ M) = (removeDo L) ★ (removeDo M)
removeDo true = true
removeDo false = false
removeDo ¿ L ⦅ T ∥ F ⦆ = ¿ removeDo L ⦅ removeDo T ∥ removeDo F ⦆
removeDo Nothing = Nothing
removeDo (Just L) = Just (removeDo L)
removeDo (M >>= F) = (removeDo M) >>= (removeDo F)
removeDo (do<- M ⁀ F) = (removeDo M) >>= (ƛ (removeDo F))


removeDoTopLvl : C ⊢ A → C ⊢ A
removeDoTopLvl (Term x) = Term x
removeDoTopLvl (ƛ L) = ƛ ( L)
removeDoTopLvl (L · M) = ( L) · ( M)
removeDoTopLvl (num x) = num x
removeDoTopLvl (L ⊹ M) = ( L) ⊹ ( M)
removeDoTopLvl (L ★ M) = ( L) ★ ( M)
removeDoTopLvl true = true
removeDoTopLvl false = false
removeDoTopLvl ¿ L ⦅ T ∥ F ⦆ = ¿  L ⦅  T ∥  F ⦆
removeDoTopLvl Nothing = Nothing
removeDoTopLvl (Just L) = Just ( L)
removeDoTopLvl (M >>= F) = ( M) >>= ( F)
removeDoTopLvl (do<- M ⁀ F) = ( M) >>= (ƛ ( F))

private
  two : ∀ {Γ} → Γ ⊢ 𝕋𝕟
  two = num 2 

  twoTimesTwo : ∀ {Γ} → Γ ⊢ 𝕋𝕟
  twoTimesTwo = two ★ two

  plus : ∅ ⊢ 𝕋𝕟 𝕋⇒ 𝕋𝕟 𝕋⇒ 𝕋𝕟
  plus = ƛ (ƛ ( ( # 1 ) ⊹  # 0 ))

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

  bindChain : ∅ ⊢ 𝕋maybe
  bindChain =
    Just (num 1) >>=
    (ƛ (Just (num 1) >>=
    (ƛ Just (# 1 ⊹ # 0))))

  exSimple : bindEx ≡ (removeDo doEx)
  exSimple = refl

  exChain : bindChain ≡ (removeDo doChain)
  exChain = refl

{-
-- TODO(YEET): Take the reduction chain from Do and convert it into the recuction chain from Bind
-}

{-
Do reduction chain:
  ξ-do₁ becomes ξ->>=₁
  β-doNothing becomes β->>=Nothing
  β-doJust becomes β->>=Just

    ((do<- Just (num 1) ⁀ Just (num 1 ⊹ (Term Z)))
    —→⟨ β-doJust 𝕍𝕟 ⟩
    Just (num 1 ⊹ num 1)
    —→⟨ ξ-JustInternal δ-⊹ ⟩
    Just (num 2) ∎)
-}

-- preserveResult : {Γ : Ctx} {A : Ty} → ∀ {N M : Γ ⊢ A} → (N —↠ M) → {Val M} → (removeDo N) —↠ M
-- preserveResult {context} {.𝕋𝕓} {true} {result} reduction {value} = reduction
-- preserveResult {context} {.𝕋𝕓} {false} {result} reduction {value} = reduction
-- preserveResult {context} {𝕋maybe} {Nothing} {result} reduction {value} = reduction
-- preserveResult {context} {type} {Term x} {result} reduction {value} = reduction
-- preserveResult {context} {.𝕋𝕟} {num x} {result} reduction {value} = reduction
--
-- preserveResult {context} {𝕋maybe} {Just og} {result} reduction {value} = {! !}
-- preserveResult {context} {A 𝕋⇒ B} {ƛ og} {.(ƛ _)} reduction {𝕍clos} = {! !}
-- preserveResult {context} {type} {og · og₁} {result} reduction {value} = {! !}
-- preserveResult {context} {.𝕋𝕟} {og ⊹ og₁} {.(num _)} reduction {𝕍𝕟} = {! !}
--
-- preserveResult {context} {.𝕋𝕟} {fst ★ snd} {.(num _)} (reduction) {𝕍𝕟} = {! !}
--
-- preserveResult {context} {type} {¿ og ⦅ og₁ ∥ og₂ ⦆} {result} reduction {value} = {! !}
-- preserveResult {context} {.𝕋maybe} {og >>= og₁} {result} reduction {value} = {! !}
-- preserveResult {context} {.𝕋maybe} {do<- og ⁀ og₁} {result} reduction {value} = {! !}

reducesSameTopLvl : {C : Ctx} {A : Ty} {v : Value A} {L : C ⊢ A} → L ↓ v → removeDoTopLvl L ↓ v
reducesSameTopLvl ↓num = ↓num
reducesSameTopLvl (↓add expr expr₁) = ↓add expr expr₁
reducesSameTopLvl (↓mul expr expr₁) = ↓mul expr expr₁
reducesSameTopLvl ↓true = ↓true
reducesSameTopLvl ↓false = ↓false
reducesSameTopLvl (↓¿true expr expr₁) = ↓¿true expr expr₁
reducesSameTopLvl (↓¿false expr expr₁) = ↓¿false expr expr₁
reducesSameTopLvl (↓lam el) = ↓lam el
reducesSameTopLvl (↓app expr expr₁ expr₂) = ↓app expr expr₁ expr₂
reducesSameTopLvl ↓nothing = ↓nothing
reducesSameTopLvl (↓just expr) = ↓just expr
reducesSameTopLvl (↓bindJust expr expr₁ expr₂) = ↓bindJust expr expr₁ expr₂
reducesSameTopLvl (↓bindNothing expr) = ↓bindNothing expr
reducesSameTopLvl (↓doNothing expr) = ↓bindNothing expr
reducesSameTopLvl {c} {.𝕋maybe} {v} {(do<- monad ⁀ expr₂)} (↓doJust expr expr₁) = ↓bindJust expr (↓lam expr₂) expr₁

-- convertReduction : (L ↓ v) → v ≅ w → (removeDo L ) ↓ w
-- convertReduction ↓num eq = {!  !}
-- convertReduction (↓add red red₁) eq = {! !}
-- convertReduction (↓mul red red₁) eq = {! !}
-- convertReduction ↓true eq = {! !}
-- convertReduction ↓false eq = {! !}
-- convertReduction (↓¿true red red₁) eq = {! !}
-- convertReduction (↓¿false red red₁) eq = {! !}
-- convertReduction (↓lam el) eq = {! !}
-- convertReduction (↓app red red₁ red₂) eq = {! !}
-- convertReduction ↓nothing eq = {! !}
-- convertReduction (↓just red) eq = {! !}
-- convertReduction (↓bindJust red red₁ red₂) eq = {! !}
-- convertReduction (↓bindNothing red) eq = {! !}
-- convertReduction (↓doJust red red₁) eq = {! !}
-- convertReduction (↓doNothing red) eq = {! !}

plusisthesame : ∀ {vl vr vln vrn} → vl ≡ vln → vr ≡ vrn → num𝕍 (vl + vr) ≅ num𝕍 (vln + vrn)
plusisthesame {vl} {vr} {vl} {vr} refl refl = num𝕍x≅num𝕍y refl

multisthesame : ∀ {vl vr vln vrn} → vl ≡ vln → vr ≡ vrn → num𝕍 (vl * vr) ≅ num𝕍 (vln * vrn)
multisthesame {vl} {vr} {vl} {vr} refl refl = num𝕍x≅num𝕍y refl

reducesEquivalent : {C : Ctx} {A : Ty} {v w : Value A} {L : C ⊢ A} → L ↓ v → removeDo L ↓ w → v ≅ w
reducesEquivalent {C} {.𝕋𝕟} {.(num𝕍 _)} {.(num𝕍 _)} {.(num _)} ↓num ↓num = num𝕍x≅num𝕍y refl
reducesEquivalent {C} {.𝕋𝕟} {(num𝕍 (x))} {(num𝕍 (y))} {(left ⊹ right)} (↓add ogr ogl) (↓add newr newl) =
  plusisthesame refl refl
reducesEquivalent {C} {.𝕋𝕟} {(num𝕍 (x))} {(num𝕍 (y))} {(left ★ right)} (↓mul ogr ogl) (↓mul newr newl) =
  multisthesame refl refl
reducesEquivalent {C} {.𝕋𝕓} {.true𝕍} {.true𝕍} {.true} ↓true ↓true = true𝕍≅true𝕍
reducesEquivalent {C} {.𝕋𝕓} {.false𝕍} {.false𝕍} {.false} ↓false ↓false = false𝕍≅false𝕍
reducesEquivalent {C} {A} {v} {w} {.(¿ _ ⦅ _ ∥ _ ⦆)} (↓¿true og og₁) (↓¿true new new₁) = reducesEquivalent og₁ new₁
reducesEquivalent {C} {A} {v} {w} {(¿ c ⦅ x ∥ y ⦆)} (↓¿true og og₁) (↓¿false new new₁) = {!  !}
reducesEquivalent {C} {A} {v} {w} {(¿ c ⦅ x ∥ y ⦆)} (↓¿false og og₁) (↓¿true new new₁) = {! !}
reducesEquivalent {C} {A} {v} {w} {.(¿ _ ⦅ _ ∥ _ ⦆)} (↓¿false og og₁) (↓¿false new new₁) = reducesEquivalent og₁ new₁
reducesEquivalent {C} {.(_ 𝕋⇒ _)} {.(clos𝕍 el)} {.(clos𝕍 (removeDo el))} {.(ƛ el)} (↓lam el) (↓lam .(removeDo el)) = {! !}
reducesEquivalent {C} {A} {v} {w} {(f · inp)} (↓app og og₁ og₂) (↓app new new₁ new₂) = {! !}
reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {.nothing𝕍} {.Nothing} ↓nothing ↓nothing = nothing𝕍≅nothing𝕍
reducesEquivalent {C} {.𝕋maybe} {(just𝕍 x)} {(just𝕍 y)} {(Just l)} (↓just og) (↓just new) = ? --reducesEquivalent og new
reducesEquivalent {C} {.𝕋maybe} {v} {w} {.(_ >>= _)} (↓bindJust og og₁ og₂) (↓bindJust new new₁ new₂) = {! !}
reducesEquivalent {C} {.𝕋maybe} {v} {.nothing𝕍} {.(_ >>= _)} (↓bindJust og og₁ og₂) (↓bindNothing new) = {! !}
reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {w} {.(_ >>= _)} (↓bindNothing og) (↓bindJust new new₁ new₂) = {! !}
reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {.nothing𝕍} {.(_ >>= _)} (↓bindNothing og) (↓bindNothing new) = reducesEquivalent og new
reducesEquivalent {C} {.𝕋maybe} {v} {w} {.(do<- _ ⁀ _)} (↓doJust og og₁) (↓bindJust new new₁ new₂) = {! !}
reducesEquivalent {C} {.𝕋maybe} {v} {.nothing𝕍} {.(do<- _ ⁀ _)} (↓doJust og og₁) (↓bindNothing new) = {! !}
reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {w} {.(do<- _ ⁀ _)} (↓doNothing og) (↓bindJust new new₁ new₂) = {! !}
reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {.nothing𝕍} {.(do<- _ ⁀ _)} (↓doNothing og) (↓bindNothing new) = reducesEquivalent og new

-- reducesEquivalent : {C : Ctx} {A : Ty} {v w : Value A} (L : C ⊢ A) → L ↓ v → ( v ≅ w ) → ( removeDo L ↓ w )
-- reducesEquivalent {C} {A} {v} {w} (Term x) () eq
-- reducesEquivalent {C} {.(_ 𝕋⇒ _)} {.(clos𝕍 l)} {w} (ƛ l) (↓lam .l) eq = {! !}
-- reducesEquivalent {C} {A} {v} {w} (l · l₁) (↓app og og₁ og₂) eq = {! !}
-- reducesEquivalent {C} {.𝕋𝕟} {.(num𝕍 x)} {w} (num x) ↓num eq = {! !}
-- reducesEquivalent {C} {.𝕋𝕟} {.(num𝕍 (_ + _))} {w} (l ⊹ l₁) (↓add og og₁) eq = {! !}
-- reducesEquivalent {C} {.𝕋𝕟} {.(num𝕍 (_ * _))} {w} (l ★ l₁) (↓mul og og₁) eq = {! !}
-- reducesEquivalent {C} {.𝕋𝕓} {.true𝕍} {w} true ↓true eq = {! ↓true !}
-- reducesEquivalent {C} {.𝕋𝕓} {.false𝕍} {w} false ↓false eq = {! !}
-- reducesEquivalent {C} {A} {v} {w} ¿ l ⦅ l₁ ∥ l₂ ⦆ (↓¿true og og₁) eq = {! !}
-- reducesEquivalent {C} {A} {v} {w} ¿ l ⦅ l₁ ∥ l₂ ⦆ (↓¿false og og₁) eq = {! !}
-- reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {w} Nothing ↓nothing eq = {! !}
-- reducesEquivalent {C} {.𝕋maybe} {.(just𝕍 _)} {w} (Just l) (↓just og) eq = {! !}
-- reducesEquivalent {C} {.𝕋maybe} {v} {w} (l >>= l₁) (↓bindJust og og₁ og₂) eq = {! !}
-- reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {w} (l >>= l₁) (↓bindNothing og) eq = {! !}
-- reducesEquivalent {C} {.𝕋maybe} {v} {w} (do<- l ⁀ l₁) (↓doJust og og₁) eq = {! !}
-- reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {w} (do<- l ⁀ l₁) (↓doNothing og) eq = {! !}



-- reducesEquivalent : {C : Ctx} {v w : Value} {A : Ty} {L : C ⊢ A} → L ↓ v → ( (removeDo L) ↓ w ) × ( v ≅ w )
-- reducesEquivalent = ?




-- from jose
-- _≡ₑ_ : ∀ {aTy rTy} → Value (aTy 𝕋⇒ rTy) → Value ({!   !} 𝕋⇒ {!   !}) → Set 
--
-- data _≡ᵣ_ : ∀ {ty} → Value ty → Value (MaybeTy→ListTy ty) → Set where
--     NothingV≡ᵣNilV : ∀ {v} → NothingV {v} ≡ᵣ NilV
--     JustV≡ᵣConsV : ∀ {ty} {vₒ : Value ty} {vₙ} → vₒ ≡ᵣ vₙ  → JustV vₒ ≡ᵣ ConsV vₙ NilV
--     NilV≡ᵣNilV : ∀ {ty} {v : Value ty} → NilV {ty} ≡ᵣ NilV
--     ConsV≡ᵣConsV : ∀ {ty} {hₒ : Value ty} {tₒ} {hₙ} {tₙ} → hₒ ≡ᵣ hₙ → tₒ ≡ᵣ tₙ → ConsV hₒ tₒ ≡ᵣ ConsV hₙ tₙ
--     LeftV≡ᵣLeftV : ∀ {ty₁ ty₂} {vₒ : Value (EitherTy ty₁ ty₂)} {vₙ} → vₒ ≡ᵣ vₙ  → LeftV {B = ty₂} vₒ ≡ᵣ LeftV vₙ
--     RightV≡ᵣRightV : ∀ {ty₁ ty₂} {vₒ : Value (EitherTy ty₁ ty₂)} {vₙ} → vₒ ≡ᵣ vₙ  → RightV {A = ty₁} vₒ ≡ᵣ RightV vₙ
--     ClosV≡ᵣClosV : {!   !} → ClosV {!   !} {!   !} ≡ᵣ ClosV {!   !} {!   !}
--
-- _≡ₑ_ = {!   !}





