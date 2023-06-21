module refactoring where

open import lang
open import Data.Product public
open import Data.Bool hiding ( _≟_ )
-- import Agda.Builtin.Unit
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst) public
open Eq.≡-Reasoning using (begin_ ; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat
open import Data.Nat.Properties

variable A B ty : Ty
variable Γ Δ C : Ctx
variable v : Value A
variable L : Γ ⊢ A
variable γ : Env Γ
variable δ : Env Δ

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
-- --     γₒ ⸴' argVₒ ⊢e bₒ ↓ retVₒ → 
-- --     (γₙ ⸴' argVₙ) ⊢e bₙ ↓ retVₙ → 
-- --     retVₒ ≡ᵣ retVₙ → 
-- --     ⊤



removeDo : Γ ⊢ A → Γ ⊢ A
removeDo (Term x) = Term x
removeDo (ƛ L) = ƛ (removeDo L)
removeDo (L · M) = (removeDo L) · (removeDo M)
removeDo (num x) = num x
removeDo (L ⊹ M) = (removeDo L) ⊹ (removeDo M)
removeDo (L ★ M) = (removeDo L) ★ (removeDo M)
removeDo true = true
removeDo false = false
-- removeDo ¿ L ⦅ T ∥ F ⦆ = ¿ removeDo L ⦅ removeDo T ∥ removeDo F ⦆
removeDo Nothing = Nothing
removeDo (Just L) = Just (removeDo L)
removeDo (M >>= F) = (removeDo M) >>= (removeDo F)
removeDo (do<- M ⁀ F) = (removeDo M) >>= (ƛ (removeDo F))

removeDoValue : Value A → Value A
removeDoEnv : Env Γ → Env Γ

removeDoEnv ∅′ = ∅′
removeDoEnv (γ ⸴′ x) = (removeDoEnv γ) ⸴′ (removeDoValue x)

removeDoValue (num𝕍 x) = num𝕍 x
removeDoValue true𝕍 = true𝕍
removeDoValue false𝕍 = false𝕍
removeDoValue (clos𝕍 body γ) = clos𝕍 (removeDo body) (removeDoEnv γ)
removeDoValue nothing𝕍 = nothing𝕍
removeDoValue (just𝕍 x) = just𝕍 x

removeDoTopLvl : ∅ ⊢ A → ∅ ⊢ A
removeDoTopLvl x = removeDo x

-- removeDoTopLvl : Γ ⊢ A → Γ ⊢ A
-- removeDoTopLvl (Term x) = Term x
-- removeDoTopLvl (ƛ L) = ƛ ( L)
-- removeDoTopLvl (L · M) = ( L) · ( M)
-- removeDoTopLvl (num x) = num x
-- removeDoTopLvl (L ⊹ M) = ( L) ⊹ ( M)
-- removeDoTopLvl (L ★ M) = ( L) ★ ( M)
-- removeDoTopLvl true = true
-- removeDoTopLvl false = false
-- -- removeDoTopLvl ¿ L ⦅ T ∥ F ⦆ = ¿  L ⦅  T ∥  F ⦆
-- removeDoTopLvl Nothing = Nothing
-- removeDoTopLvl (Just L) = Just ( L)
-- removeDoTopLvl (M >>= F) = ( M) >>= ( F)
-- removeDoTopLvl (do<- M ⁀ F) = ( M) >>= (ƛ ( F))

data _≅_ : (v : Value ty) → (w : Value ty) → Set where
  num𝕍x≅num𝕍y : ∀ {x y}
    → x ≡ y
    → (num𝕍 x) ≅ (num𝕍 y)
  true𝕍≅true𝕍 : true𝕍 ≅ true𝕍
  false𝕍≅false𝕍 : false𝕍 ≅ false𝕍
  nothing𝕍≅nothing𝕍 : nothing𝕍 ≅ nothing𝕍
  just𝕍≅just𝕍 : {x y : ℕ} → x ≡ y → (just𝕍 x) ≅ (just𝕍 y)
  -- clos𝕍≅clos𝕍 : {aTy rTy : Ty} {f g : C ⸴ aTy ⊢ rTy}
  --   → ∀ { ArgV : Value aTy }
  --   → { retVf retVg : Value rTy }
  --   → γ ⊨ f ↓ retVf
  --   → γ ⊨ g ↓ retVg
  --   → retVf ≅ retVg
  --   → clos𝕍 f ≅ clos𝕍 g 
  tempEquiv : (body : (Γ ⸴ A) ⊢ B) → clos𝕍 body γ ≅ clos𝕍 (removeDo body) (removeDoEnv γ)
  sameEquiv : (body : (Γ ⸴ A) ⊢ B) → clos𝕍 body γ ≅ clos𝕍 body γ


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

-- reducesSameTopLvl : {A : Ty} {v : Value A} {L : Γ ⊢ A} → γ ⊨ L ↓ v → γ ⊨ removeDoTopLvl L ↓ v
-- reducesSameTopLvl ↓num = ↓num
-- reducesSameTopLvl (↓add expr expr₁) = ↓add expr expr₁
-- reducesSameTopLvl (↓mul expr expr₁) = ↓mul expr expr₁
-- reducesSameTopLvl ↓true = ?
-- reducesSameTopLvl ↓false = ?
-- -- reducesSameTopLvl (↓¿true expr expr₁) = ↓¿true expr expr₁
-- -- reducesSameTopLvl (↓¿false expr expr₁) = ↓¿false expr expr₁
-- reducesSameTopLvl (↓lam) = ↓lam
-- reducesSameTopLvl (↓app expr expr₁ expr₂) = ↓app expr expr₁ expr₂
-- reducesSameTopLvl ↓nothing = ↓nothing
-- reducesSameTopLvl (↓just expr) = ↓just expr
-- reducesSameTopLvl (↓bindJust expr expr₁ expr₂) = ↓bindJust expr expr₁ expr₂
-- reducesSameTopLvl (↓bindNothing expr) = ↓bindNothing expr
-- reducesSameTopLvl (↓doNothing expr) = ↓bindNothing expr
-- reducesSameTopLvl x = ?
-- reducesSameTopLvl {c} {.𝕋maybe} {v} {(do<- monad ⁀ expr₂)} (↓doJust expr expr₁) = ↓bindJust expr (↓lam expr₂) expr₁

valuetonumber : (n : Value 𝕋𝕟) → ℕ
valuetonumber (num𝕍 x) = x

plusisthesame : ∀ {vl vr vln vrn : ℕ} → vl ≡ vln → vr ≡ vrn → num𝕍 (vl + vr) ≅ num𝕍 (vln + vrn)
plusisthesame {vl} {vr} {vl} {vr} refl refl = num𝕍x≅num𝕍y refl

multisthesame : ∀ {vl vr vln vrn} → vl ≡ vln → vr ≡ vrn → num𝕍 (vl * vr) ≅ num𝕍 (vln * vrn)
multisthesame {vl} {vr} {vl} {vr} refl refl = num𝕍x≅num𝕍y refl

valEquiv : (x : Value A) → x ≅ (removeDoValue x)
valEquiv (num𝕍 x) = num𝕍x≅num𝕍y refl
valEquiv true𝕍 = true𝕍≅true𝕍
valEquiv false𝕍 = false𝕍≅false𝕍
valEquiv (clos𝕍 body x) = tempEquiv body
valEquiv nothing𝕍 = nothing𝕍≅nothing𝕍
valEquiv (just𝕍 x) = just𝕍≅just𝕍 refl

environmentRemainsEquivalent : {p : Γ ∋ A} → (valueLookup γ p) ≅ (valueLookup (removeDoEnv γ) p)
environmentRemainsEquivalent {(_ ⸴ A)} {A} γ@{_ ⸴′ x} {Z} = valEquiv x -- (valueLookup γ Z) ≅ (valueLookup (removeDoEnv γ) Z)
environmentRemainsEquivalent {(Γ ⸴ _)} {A} {γ ⸴′ _} {S p} = environmentRemainsEquivalent {Γ} {A} {γ} {p}

environmentRefactorsInternalValue : {p : Γ ∋ A} → (removeDoValue (valueLookup γ p)) ≡ (valueLookup (removeDoEnv γ) p)
environmentRefactorsInternalValue {(_ ⸴ A)} {A} {γ ⸴′ x} {Z} = refl
environmentRefactorsInternalValue {(Γ ⸴ _)} {A} {γ ⸴′ _} {S p} = environmentRefactorsInternalValue {Γ} {A} {γ} {p}

-- TODO prove that the full terms are equal given that environmentRefactorsInternalValue holds
helpgod : {p : Γ ∋ A} → removeDoEnv γ ⊨ removeDo (Term p) ↓ valueLookup (removeDoEnv γ) p ≡ removeDoEnv γ ⊨ removeDo (Term p) ↓ removeDoValue (valueLookup γ p)
helpgod {_ ⸴ _} {_} {_ ⸴′ _} {Z} = refl
helpgod {Γ ⸴ _} {A} {γ ⸴′ _} {S p} = ? -- TODO: try cong or subst -- helpgod {Γ} {A} {γ} {p}


-- helpmeplease : {Γ : Ctx} {A : Ty} {γ : Env Γ} {p : Γ ∋ A} → removeDoEnv γ ⊨ removeDo (Term p) ↓ valueLookup (removeDoEnv γ) p → removeDoEnv γ ⊨ removeDo (Term p) ↓ removeDoValue (valueLookup γ p)
-- helpmeplease {Γ} {A} {γ} {p} x = {! x !}


reducesEquivalentOther : {A : Ty} {v : Value A} {L : Γ ⊢ A} → γ ⊨ L ↓ v → (removeDoEnv γ) ⊨ (removeDo L) ↓ (removeDoValue v)
reducesEquivalentOther {Γ} {γ} {A} {.(valueLookup γ p)} {(Term p)} (↓var {Γ} {A} {γ} {p}) = ?
  where
  valLoopup = valueLookup (removeDoEnv γ) p
  retval = removeDoValue (valueLookup γ p)
  proof = environmentRefactorsInternalValue {Γ} {A} {γ} {p}
  red = ↓var {Γ} {A} {removeDoEnv γ} {p}
  -- helpme = subst (λ x → x) {! proof !} (red)
reducesEquivalentOther {Γ} {γ} {.𝕋𝕟} {.(num𝕍 _)} {.(num _)} ↓num = ↓num
reducesEquivalentOther {Γ} {γ} {.𝕋𝕟} {.(num𝕍 (_))} {.(_ ⊹ _)} (↓add red red₁) = ↓add (reducesEquivalentOther red) (reducesEquivalentOther red₁)
reducesEquivalentOther {Γ} {γ} {.𝕋𝕟} {.(num𝕍 (_))} {.(_ ★ _)} (↓mul red red₁) = ↓mul (reducesEquivalentOther red) (reducesEquivalentOther red₁)
reducesEquivalentOther {Γ} {γ} {.(_ 𝕋⇒ _)} {.(clos𝕍 _ γ)} {.(ƛ _)} ↓lam = ↓lam
reducesEquivalentOther {Γ} {γ} {A} {v} {.(_ · _)} (↓app red red₁ red₂) = ↓app (reducesEquivalentOther red) (reducesEquivalentOther red₁) (reducesEquivalentOther red₂)
reducesEquivalentOther {Γ} {γ} {.𝕋maybe} {.nothing𝕍} {.Nothing} ↓nothing = ↓nothing
reducesEquivalentOther {Γ} {γ} {.𝕋maybe} {.(just𝕍 _)} {.(Just _)} (↓just red) = ↓just (reducesEquivalentOther red)
reducesEquivalentOther {Γ} {γ} {.𝕋maybe} {v} {.(_ >>= _)} (↓bindJust red red₁ red₂) = {! !}
reducesEquivalentOther {Γ} {γ} {.𝕋maybe} {.nothing𝕍} {.(_ >>= _)} (↓bindNothing red) = ↓bindNothing (reducesEquivalentOther red)
reducesEquivalentOther {Γ} {γ} {.𝕋maybe} {v} {.(do<- _ ⁀ _)} (↓doJust red red₁) = {! !}
reducesEquivalentOther {Γ} {γ} {.𝕋maybe} {.nothing𝕍} {.(do<- _ ⁀ _)} (↓doNothing red) = ↓bindNothing (reducesEquivalentOther red)

reducesEquivalent : {A : Ty} {v : Value A} {L : Γ ⊢ A} → γ ⊨ L ↓ v → ∃[ w ] ( ((removeDoEnv γ) ⊨ (removeDo L) ↓ w) × ( v ≅ w ) )

-- -- Produce the value that the refactored function should produce
-- proj₁ (reducesEquivalent {Γ} {γ} {𝕋𝕟} {num𝕍 x} {lang} red) = num𝕍 x
-- proj₁ (reducesEquivalent {Γ} {γ} {𝕋𝕓} {true𝕍} {lang} red) = true𝕍
-- proj₁ (reducesEquivalent {Γ} {γ} {𝕋𝕓} {false𝕍} {lang} red) = false𝕍
-- proj₁ (reducesEquivalent {Γ} {γ} {(D 𝕋⇒ E)} {clos𝕍 body δ} {lang} red) = (valueLookup γ ?) -- clos𝕍 (removeDo body) (removeDoEnv δ)
-- proj₁ (reducesEquivalent {Γ} {γ} {𝕋maybe} {nothing𝕍} {lang} red) = nothing𝕍
-- proj₁ (reducesEquivalent {Γ} {γ} {𝕋maybe} {just𝕍 x} {lang} red) = just𝕍 x
-- proj₁ (reducesEquivalent {Γ} {γ} {ty} {val} {lang} (↓var {Γ} {A} {γ} {p})) = valueLookup (removeDoEnv γ) p
proj₁ (reducesEquivalent {Γ} {γ} {ty} {val} {lang} red) = removeDoValue (val) -- (valueLookup (removeDoEnv γ) ?)

-- proj₁ (proj₂ (reducesEquivalent red )) = ?

-- Provide the reduction to that value
proj₁ (proj₂ (reducesEquivalent {Γ} {γ} {A} {.(valueLookup γ p)} {(Term p)} (↓var {Γ} {A} {γ} {p}))) = {! !} -- ↓var {Γ} {A} {removeDoEnv γ} {p} 
proj₁ (proj₂ (reducesEquivalent {Γ} {γ} {.𝕋𝕟} {.(num𝕍 _)} {.(num _)} (↓num ))) = ↓num
proj₁ (proj₂ (reducesEquivalent {Γ} {γ} {.𝕋𝕟} {.(num𝕍 (_))} {.(_ ⊹ _)} (↓add x y))) = ↓add newleftred newrightred
  where
    newleftred  = proj₁ ( proj₂ (reducesEquivalent x) )
    newrightred = proj₁ ( proj₂ (reducesEquivalent y) )
proj₁ (proj₂ (reducesEquivalent {Γ} {γ} {.𝕋𝕟} {.(num𝕍 (_))} {.(_ ★ _)} (↓mul x y))) = ↓mul newleftred newrightred
  where
    newleftred  = proj₁ ( proj₂ (reducesEquivalent x) )
    newrightred = proj₁ ( proj₂ (reducesEquivalent y) )
proj₁ (proj₂ (reducesEquivalent {Γ} {γ} {(A 𝕋⇒ B)} {.(clos𝕍 _ γ)} {.(ƛ _)} (↓lam {Γ} {A} {B} {γ} {body} ))) = ↓lam {Γ} {A} {B} {removeDoEnv γ} 
proj₁ (proj₂ (reducesEquivalent {Γ} {γ} {A} {val} {(fun · inp)} (↓app funred inpred resred))) = {! !} -- ↓app newfunred newinpred {! !}
  where
    newfunred = proj₁ (proj₂ (reducesEquivalent funred))
    newinpred = proj₁ (proj₂ (reducesEquivalent inpred))
    newinpval = proj₁ (reducesEquivalent inpred)
    newfunval = proj₁ (reducesEquivalent funred)
    newresred = proj₁ (proj₂ (reducesEquivalent {(Γ ⸴ A)} {(γ ⸴′ {! !})} {! !}))
proj₁ (proj₂ (reducesEquivalent {Γ} {γ} {.𝕋maybe} {.nothing𝕍} {.Nothing} ↓nothing)) = ↓nothing
proj₁ (proj₂ (reducesEquivalent {Γ} {γ} {.𝕋maybe} {.(just𝕍 _)} {.(Just _)} (↓just intred))) = {! !} -- ↓just newintred
  where
    newintred = proj₁ (proj₂ (reducesEquivalent intred))
proj₁ (proj₂ (reducesEquivalent {Γ} {γ} {.𝕋maybe} {val} {.(_ >>= _)} (↓bindJust monadred funred bodyred))) = {! !} --  ↓bindJust newmonadred newfunred {!   !}
  where
    newmonadred = proj₁ (proj₂ (reducesEquivalent monadred))
    newfunred   = proj₁ (proj₂ (reducesEquivalent funred ))
    newbodyred  = proj₁ (proj₂ (reducesEquivalent bodyred ))
proj₁ (proj₂ (reducesEquivalent {Γ} {γ} {.𝕋maybe} {.nothing𝕍} {.(_ >>= _)} (↓bindNothing red))) = {! !}
proj₁ (proj₂ (reducesEquivalent {Γ} {γ} {.𝕋maybe} {val} {.(do<- _ ⁀ _)} (↓doJust red red₁))) = {! !}
proj₁ (proj₂ (reducesEquivalent {Γ} {γ} {.𝕋maybe} {.nothing𝕍} {.(do<- _ ⁀ _)} (↓doNothing red))) = {! !}

-- State equivalence of that value with the original value
-- proj₂ (proj₂ (reducesEquivalent {Γ} {γ} {.𝕋𝕟} {num𝕍 x} {lang} red)) = num𝕍x≅num𝕍y refl
-- proj₂ (proj₂ (reducesEquivalent {Γ} {γ} {.𝕋𝕓} {true𝕍} {lang} red)) = true𝕍≅true𝕍
-- proj₂ (proj₂ (reducesEquivalent {Γ} {γ} {.𝕋𝕓} {false𝕍} {lang} red)) = false𝕍≅false𝕍
-- proj₂ (proj₂ (reducesEquivalent {Γ} {γ} {.(_ 𝕋⇒ _)} {clos𝕍 body x} {lang} red)) = tempEquiv body
-- proj₂ (proj₂ (reducesEquivalent {Γ} {γ} {.𝕋maybe} {nothing𝕍} {lang} red)) = nothing𝕍≅nothing𝕍
-- proj₂ (proj₂ (reducesEquivalent {Γ} {γ} {.𝕋maybe} {just𝕍 x} {lang} red)) = just𝕍≅just𝕍 refl
proj₂ (proj₂ (reducesEquivalent {Γ} {γ} {ty} {val} {lang} red)) = valEquiv val
-- proj₂ (proj₂ (reducesEquivalent red)) = ?

-- -- Construct the value which we will prove is equivalent and the result of `removeDo`
-- proj₁ (reducesEquivalent {c} {env} {.𝕋𝕟} {num𝕍 n} {l} x) = num𝕍 n 
-- proj₁ (reducesEquivalent {c} {env} {.𝕋𝕓} {true𝕍} {l} x) = true𝕍
-- proj₁ (reducesEquivalent {c} {env} {.𝕋𝕓} {false𝕍} {l} x) = false𝕍
-- proj₁ (reducesEquivalent {c} {env} {.(_ 𝕋⇒ _)} {clos𝕍 body δ} {l} x) = clos𝕍 (removeDo body) δ
-- proj₁ (reducesEquivalent {c} {env} {.𝕋maybe} {nothing𝕍} {l} x) = nothing𝕍
-- proj₁ (reducesEquivalent {c} {env} {.𝕋maybe} {just𝕍 n} {l} x) = just𝕍 n
--
-- -- Prove that the refactored function reduces to that value
-- proj₁ (proj₂ (reducesEquivalent {c} {env} {.𝕋𝕟} {.(num𝕍 _)} {.(num _)} ↓num)) = ↓num
-- proj₁ (proj₂ (reducesEquivalent {c} {env} {.𝕋𝕟} {(num𝕍 (res))} {(left ⊹ right)} (↓add x y))) = ↓add newleftred newrightred
--   where
--     -- leftval  = valuetonumber ( proj₁ (reducesEquivalent x) )
--     -- rightval = valuetonumber ( proj₁ (reducesEquivalent x) )
--     newleftred  = proj₁ ( proj₂ (reducesEquivalent x) )
--     newrightred = proj₁ ( proj₂ (reducesEquivalent y) )
--     -- leftequiv  = proj₂ ( proj₂ (reducesEquivalent x) )
--     -- rightequiv = proj₂ ( proj₂ (reducesEquivalent y) )
-- proj₁ (proj₂ (reducesEquivalent {c} {env} {.𝕋𝕟} {(num𝕍 (res))} {(left ★ right)} (↓mul x y))) = ↓mul newleftred newrightred
--   where
--     newleftred  = proj₁ ( proj₂ (reducesEquivalent x) )
--     newrightred = proj₁ ( proj₂ (reducesEquivalent y) )
-- -- proj₁ (proj₂ (reducesEquivalent {c} {env} {ty} {val} {lang} ↓true)) = {! !}
-- -- proj₁ (proj₂ (reducesEquivalent {c} {env} {ty} {val} {lang} ↓false)) = {! !}
-- proj₁ (proj₂ (reducesEquivalent {c} {env} {.(_ 𝕋⇒ _)} {closure} {lang} (↓lam))) = ↓lam 
-- proj₁ (proj₂ (reducesEquivalent {c} {env} {ty} {val} {(fun · inp)} (↓app funR inpR red))) = ↓app funred inpred {!  !}
--   where
--     funred = proj₁ (proj₂ (reducesEquivalent funR))
--     inpred = proj₁ (proj₂ (reducesEquivalent inpR))
--     totred = proj₁ (proj₂ (reducesEquivalent red))
--     inpeqv = proj₂ (proj₂ (reducesEquivalent inpR))
--     inpval = proj₁ (reducesEquivalent inpR)
--     -- idea: postulate some proof that in equivalent input⸴ substitution maintains equivalence
--     -- alternatively: switch to environments
-- proj₁ (proj₂ (reducesEquivalent {c} {env} {𝕋maybe} {nothing𝕍} {Nothing} ↓nothing)) = ↓nothing
-- proj₁ (proj₂ (reducesEquivalent {c} {env} {.𝕋maybe} {(just𝕍 n)} {(Just expr)} (↓just x))) = ↓just newred
--   where
--     newred = proj₁ (proj₂ (reducesEquivalent x))
-- proj₁ (proj₂ (reducesEquivalent {c} {env} {.𝕋maybe} {just𝕍 n} {(monad >>= lam)} (↓bindJust mon↓just lam↓body red))) = ↓bindJust funred inpred {! !}
--   where
--     funred = proj₁ (proj₂ (reducesEquivalent mon↓just))
--     inpred = proj₁ (proj₂ (reducesEquivalent lam↓body))
-- proj₁ (proj₂ (reducesEquivalent {c} {env} {.𝕋maybe} {nothing𝕍} {(monad >>= lam)} (↓bindJust mon↓just lam↓body red))) = ↓bindJust funred inpred {! !}
--   where
--     funred = proj₁ (proj₂ (reducesEquivalent mon↓just))
--     inpred = proj₁ (proj₂ (reducesEquivalent lam↓body))
-- proj₁ (proj₂ (reducesEquivalent {c} {env} {.𝕋maybe} {nothing𝕍} {(monad >>= lam)} (↓bindNothing x))) = ↓bindNothing newred
--   where
--     newred = proj₁ (proj₂ (reducesEquivalent x) )
--
-- -- reducesSameTopLvl {c} {.𝕋maybe} {v} {(do<- monad ⁀ expr₂)} (↓doJust expr expr₁) = ↓bindJust expr (↓lam expr₂) expr₁
-- proj₁ (proj₂ (reducesEquivalent {c} {env} {.𝕋maybe} {just𝕍 n} {do<- monad ⁀ body} (↓doJust mon↓just red))) = ↓bindJust funred inpred {! !}
--   where
--     funred = proj₁ (proj₂ (reducesEquivalent mon↓just))
--     inpred = proj₁ (proj₂ (reducesEquivalent (↓lam )))
-- proj₁ (proj₂ (reducesEquivalent {c} {env} {.𝕋maybe} {nothing𝕍} {do<- monad ⁀ body} (↓doJust mon↓just red))) = ↓bindJust funred inpred {! !}
--   where
--     funred = proj₁ (proj₂ (reducesEquivalent mon↓just))
--     inpred = proj₁ (proj₂ (reducesEquivalent (↓lam )))
-- proj₁ (proj₂ (reducesEquivalent {c} {env} {.𝕋maybe} {nothing𝕍} {do<- monad ⁀ body} (↓doNothing x))) = ↓bindNothing newred
--   where
--     newred = proj₁ (proj₂ (reducesEquivalent x) )
--
-- -- Prove that that value is equivalent to the original value
-- proj₂ (proj₂ (reducesEquivalent {c} {env} {.𝕋𝕟} {num𝕍 x₁} {l} x)) = num𝕍x≅num𝕍y refl
-- proj₂ (proj₂ (reducesEquivalent {c} {env} {.𝕋𝕓} {true𝕍} {l} x)) = true𝕍≅true𝕍
-- proj₂ (proj₂ (reducesEquivalent {c} {env} {.𝕋𝕓} {false𝕍} {l} x)) = false𝕍≅false𝕍
-- proj₂ (proj₂ (reducesEquivalent {c} {env} {.𝕋maybe} {nothing𝕍} {l} x)) = nothing𝕍≅nothing𝕍
-- proj₂ (proj₂ (reducesEquivalent {c} {env} {.𝕋maybe} {just𝕍 x₁} {l} x)) = just𝕍≅just𝕍 refl
-- proj₂ (proj₂ (reducesEquivalent {c} {env} {(A 𝕋⇒ B)} {clos𝕍 body δ} {l} x)) = tempequiv body
--
--
-- -- reducesEquivalent {C} {.𝕋𝕟} {.(num𝕍 _)} {.(num𝕍 _)} {.(num _)} ↓num ↓num = num𝕍x≅num𝕍y refl
-- -- reducesEquivalent {C} {.𝕋𝕟} {(num𝕍 (x))} {(num𝕍 (y))} {(left ⊹ right)} (↓add ogr ogl) (↓add newr newl) =
-- --   plusisthesame refl refl
-- -- reducesEquivalent {C} {.𝕋𝕟} {(num𝕍 (x))} {(num𝕍 (y))} {(left ★ right)} (↓mul ogr ogl) (↓mul newr newl) =
-- --   multisthesame refl refl
-- -- reducesEquivalent {C} {.𝕋𝕓} {.true𝕍} {.true𝕍} {.true} ↓true ↓true = true𝕍≅true𝕍
-- -- reducesEquivalent {C} {.𝕋𝕓} {.false𝕍} {.false𝕍} {.false} ↓false ↓false = false𝕍≅false𝕍
-- -- reducesEquivalent {C} {A} {v} {w} {.(¿ _ ⦅ _ ∥ _ ⦆)} (↓¿true og og₁) (↓¿true new new₁) = reducesEquivalent og₁ new₁
-- -- reducesEquivalent {C} {A} {v} {w} {(¿ c ⦅ x ∥ y ⦆)} (↓¿true og og₁) (↓¿false new new₁) = {!  !}
-- -- reducesEquivalent {C} {A} {v} {w} {(¿ c ⦅ x ∥ y ⦆)} (↓¿false og og₁) (↓¿true new new₁) = {! !}
-- -- reducesEquivalent {C} {A} {v} {w} {.(¿ _ ⦅ _ ∥ _ ⦆)} (↓¿false og og₁) (↓¿false new new₁) = reducesEquivalent og₁ new₁
-- -- reducesEquivalent {C} {.(_ 𝕋⇒ _)} {.(clos𝕍 el)} {.(clos𝕍 (removeDo el))} {.(ƛ el)} (↓lam el) (↓lam .(removeDo el)) = {! !}
-- -- reducesEquivalent {C} {A} {v} {w} {(f · inp)} (↓app og og₁ og₂) (↓app new new₁ new₂) = {! !}
-- -- reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {.nothing𝕍} {.Nothing} ↓nothing ↓nothing = nothing𝕍≅nothing𝕍
-- -- reducesEquivalent {C} {.𝕋maybe} {(just𝕍 x)} {(just𝕍 y)} {(Just l)} (↓just og) (↓just new) = ? --reducesEquivalent og new
-- -- reducesEquivalent {C} {.𝕋maybe} {v} {w} {.(_ >>= _)} (↓bindJust og og₁ og₂) (↓bindJust new new₁ new₂) = {! !}
-- -- reducesEquivalent {C} {.𝕋maybe} {v} {.nothing𝕍} {.(_ >>= _)} (↓bindJust og og₁ og₂) (↓bindNothing new) = {! !}
-- -- reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {w} {.(_ >>= _)} (↓bindNothing og) (↓bindJust new new₁ new₂) = {! !}
-- -- reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {.nothing𝕍} {.(_ >>= _)} (↓bindNothing og) (↓bindNothing new) = reducesEquivalent og new
-- -- reducesEquivalent {C} {.𝕋maybe} {v} {w} {.(do<- _ ⁀ _)} (↓doJust og og₁) (↓bindJust new new₁ new₂) = {! !}
-- -- reducesEquivalent {C} {.𝕋maybe} {v} {.nothing𝕍} {.(do<- _ ⁀ _)} (↓doJust og og₁) (↓bindNothing new) = {! !}
-- -- reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {w} {.(do<- _ ⁀ _)} (↓doNothing og) (↓bindJust new new₁ new₂) = {! !}
-- -- reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {.nothing𝕍} {.(do<- _ ⁀ _)} (↓doNothing og) (↓bindNothing new) = reducesEquivalent og new
--
-- -- reducesEquivalent : {C : Ctx} {A : Ty} {v w : Value A} (L : C ⊢ A) → L ↓ v → ( v ≅ w ) → ( removeDo L ↓ w )
-- -- reducesEquivalent {C} {A} {v} {w} (Term x) () eq
-- -- reducesEquivalent {C} {.(_ 𝕋⇒ _)} {.(clos𝕍 l)} {w} (ƛ l) (↓lam .l) eq = {! !}
-- -- reducesEquivalent {C} {A} {v} {w} (l · l₁) (↓app og og₁ og₂) eq = {! !}
-- -- reducesEquivalent {C} {.𝕋𝕟} {.(num𝕍 x)} {w} (num x) ↓num eq = {! !}
-- -- reducesEquivalent {C} {.𝕋𝕟} {.(num𝕍 (_ + _))} {w} (l ⊹ l₁) (↓add og og₁) eq = {! !}
-- -- reducesEquivalent {C} {.𝕋𝕟} {.(num𝕍 (_ * _))} {w} (l ★ l₁) (↓mul og og₁) eq = {! !}
-- -- reducesEquivalent {C} {.𝕋𝕓} {.true𝕍} {w} true ↓true eq = {! ↓true !}
-- -- reducesEquivalent {C} {.𝕋𝕓} {.false𝕍} {w} false ↓false eq = {! !}
-- -- reducesEquivalent {C} {A} {v} {w} ¿ l ⦅ l₁ ∥ l₂ ⦆ (↓¿true og og₁) eq = {! !}
-- -- reducesEquivalent {C} {A} {v} {w} ¿ l ⦅ l₁ ∥ l₂ ⦆ (↓¿false og og₁) eq = {! !}
-- -- reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {w} Nothing ↓nothing eq = {! !}
-- -- reducesEquivalent {C} {.𝕋maybe} {.(just𝕍 _)} {w} (Just l) (↓just og) eq = {! !}
-- -- reducesEquivalent {C} {.𝕋maybe} {v} {w} (l >>= l₁) (↓bindJust og og₁ og₂) eq = {! !}
-- -- reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {w} (l >>= l₁) (↓bindNothing og) eq = {! !}
-- -- reducesEquivalent {C} {.𝕋maybe} {v} {w} (do<- l ⁀ l₁) (↓doJust og og₁) eq = {! !}
-- -- reducesEquivalent {C} {.𝕋maybe} {.nothing𝕍} {w} (do<- l ⁀ l₁) (↓doNothing og) eq = {! !}
--
--
--
-- -- reducesEquivalent : {C : Ctx} {v w : Value} {A : Ty} {L : C ⊢ A} → L ↓ v → ( (removeDo L) ↓ w ) × ( v ≅ w )
-- -- reducesEquivalent = ?
--
--
--
--
-- -- from jose
-- -- _≡ₑ_ : ∀ {aTy rTy} → Value (aTy 𝕋⇒ rTy) → Value ({!   !} 𝕋⇒ {!   !}) → Set 
-- --
-- -- data _≡ᵣ_ : ∀ {ty} → Value ty → Value (MaybeTy→ListTy ty) → Set where
-- --     NothingV≡ᵣNilV : ∀ {v} → NothingV {v} ≡ᵣ NilV
-- --     JustV≡ᵣConsV : ∀ {ty} {vₒ : Value ty} {vₙ} → vₒ ≡ᵣ vₙ  → JustV vₒ ≡ᵣ ConsV vₙ NilV
-- --     NilV≡ᵣNilV : ∀ {ty} {v : Value ty} → NilV {ty} ≡ᵣ NilV
-- --     ConsV≡ᵣConsV : ∀ {ty} {hₒ : Value ty} {tₒ} {hₙ} {tₙ} → hₒ ≡ᵣ hₙ → tₒ ≡ᵣ tₙ → ConsV hₒ tₒ ≡ᵣ ConsV hₙ tₙ
-- --     LeftV≡ᵣLeftV : ∀ {ty₁ ty₂} {vₒ : Value (EitherTy ty₁ ty₂)} {vₙ} → vₒ ≡ᵣ vₙ  → LeftV {B = ty₂} vₒ ≡ᵣ LeftV vₙ
-- --     RightV≡ᵣRightV : ∀ {ty₁ ty₂} {vₒ : Value (EitherTy ty₁ ty₂)} {vₙ} → vₒ ≡ᵣ vₙ  → RightV {A = ty₁} vₒ ≡ᵣ RightV vₙ
-- --     ClosV≡ᵣClosV : {!   !} → ClosV {!   !} {!   !} ≡ᵣ ClosV {!   !} {!   !}
-- --
-- -- _≡ₑ_ = {!   !}
--
--
--
--
--
reducesEquivalentTopLvl : {A : Ty} {v : Value A} {L : ∅ ⊢ A} → ∅′ ⊨ L ↓ v → ∃[ w ] ( (∅′ ⊨ (removeDoTopLvl L) ↓ w) × ( v ≅ w ) )
reducesEquivalentTopLvl x = reducesEquivalent x
