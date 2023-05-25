module refactoring where

open import lang

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

preserveResult : {Γ : Ctx} {A : Ty} → ∀ {N M : Γ ⊢ A} → (N —↠ M) → {Val M} → (removeDo N) —↠ M
preserveResult {context} {.𝕋𝕓} {true} {result} reduction {value} = reduction
preserveResult {context} {.𝕋𝕓} {false} {result} reduction {value} = reduction
preserveResult {context} {𝕋maybe} {Nothing} {result} reduction {value} = reduction
preserveResult {context} {type} {Term x} {result} reduction {value} = reduction
preserveResult {context} {.𝕋𝕟} {num x} {result} reduction {value} = reduction

preserveResult {context} {𝕋maybe} {Just og} {result} reduction {value} = {! !}
preserveResult {context} {A 𝕋⇒ B} {ƛ og} {.(ƛ _)} reduction {𝕍clos} = {! !}
preserveResult {context} {type} {og · og₁} {result} reduction {value} = {! !}
preserveResult {context} {.𝕋𝕟} {og ⊹ og₁} {.(num _)} reduction {𝕍𝕟} = {! !}

preserveResult {context} {.𝕋𝕟} {fst ★ snd} {.(num _)} (reduction) {𝕍𝕟} = {! !}

preserveResult {context} {type} {¿ og ⦅ og₁ ∥ og₂ ⦆} {result} reduction {value} = {! !}
preserveResult {context} {.𝕋maybe} {og >>= og₁} {result} reduction {value} = {! !}
preserveResult {context} {.𝕋maybe} {do<- og ⁀ og₁} {result} reduction {value} = {! !}
