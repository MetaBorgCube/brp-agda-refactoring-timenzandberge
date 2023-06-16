module refactoring where

open import lang
open import Data.Product public

-- Contextual equivalence
_≅_ : {ty : Ty} (v : Value ty) → (w : Value ty) → Set
num𝕍 x ≅ num𝕍 y = x ≡ y
true𝕍 ≅ true𝕍 = ⊤
true𝕍 ≅ false𝕍 = ⊥
false𝕍 ≅ true𝕍 = ⊥
false𝕍 ≅ false𝕍 = ⊤
nothing𝕍 ≅ nothing𝕍 = ⊤
nothing𝕍 ≅ just𝕍 x = ⊥
just𝕍 x ≅ nothing𝕍 = ⊥
just𝕍 x ≅ just𝕍 y = x ≡ y
clos𝕍 {Γ} {aTy} {rTy} f ≅ clos𝕍 {Δ} g =
  ∀ { ArgV : Value aTy }
  → { retVf retVg : Value rTy }
  → retVf ≅ retVg
  → f ↓ retVf
  → g ↓ retVg
  → ⊤

  
-- ClosV {argTy = argTy} {retTy} γₒ bₒ ≡ᵣ ClosV γₙ bₙ = 
--     ∀ {argVₒ : Value argTy} {argVₙ : Value (MaybeTy→ListTy argTy)} {argVₒ≡ᵣargV : argVₒ ≡ᵣ argVₙ} 
--     {retVₒ : Value retTy} {retVₙ : Value (MaybeTy→ListTy retTy)} → 
--     γₒ ,' argVₒ ⊢e bₒ ↓ retVₒ → 
--     (γₙ ,' argVₙ) ⊢e bₙ ↓ retVₙ → 
--     retVₒ ≡ᵣ retVₙ → 
--     ⊤


removeDo : ∀ {C : Ctx} {A : Ty} → C ⊢ A → C ⊢ A
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


removeDoTopLvl : ∀ {C : Ctx} {A : Ty} → C ⊢ A → C ⊢ A
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

  2+2=4 : plus · two · two —↠ ( num 4 )
  2+2=4 = begin
    ((ƛ (ƛ ((Term (S Z)) ⊹ (Term Z)))) · num 2 · num 2 —→⟨
      ξ-·₁ (β-ƛ 𝕍𝕟) ⟩
      (ƛ (num 2 ⊹ (Term Z))) · num 2 —→⟨ β-ƛ 𝕍𝕟 ⟩
      (num 2 ⊹ num 2) —→⟨ δ-⊹ ⟩ num 4 ∎)

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


 

  
