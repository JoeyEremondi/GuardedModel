{-# OPTIONS --cubical --guarded --prop --rewriting #-}


open import Source.SyntaxParams
open import Source.Tele {{CastCalc}}

module Source.Redex  {{_ : Inductives}} {{_ : IndParams}}  where

open import DecPEq
open import Cubical.Data.Nat
import Source.Syntax
open Source.Syntax {{CastCalc}}
open import Cubical.Data.Equality hiding (Sub)
open import Cubical.Data.Vec as V
open import Cubical.Data.Sum
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Bool
open import Cubical.HITs.SetQuotients


open import Syntax using (Sig ; ν ;  ■ )

open import Cubical.Data.List hiding ([_])

open import Source.SubProperties

private variable
  t  t₁  t₂ t₃ t₀ T T₁ T₂ T'₁ T'₂ T₃ T₄ ε : AST
  c : CName
  d : DName c
  i : ℕ

{-# DISPLAY Source.Syntax.ABT→AST = ABT→AST  #-}
{-# DISPLAY Source.Syntax.AST→ABT = AST→ABT  #-}
{-# DISPLAY Syntax.ABTOps._⨟_ = _⨟_  #-}
{-# DISPLAY Syntax.ABTOps.⟪_⟫ = ⟪_⟫  #-}
-- {-# DISPLAY ABTOps.⟪_⟫ Op sig x = ⟪ x ⟫  #-}
-- {-# DISPLAY Syntax.ABTOps.⟪_⟫ Op sig x = ⟪ x ⟫  #-}


data Redex : AST → Set where
  [β] : ∀ t t₂ →
    ----------------------------------------
    Redex ((λx⦂ T ∙ t) $ t₂)

  [J] : ∀ T t₁ t₂ t ε →
    ----------------------------------------
    Redex (SJ T t₁ t₂ t (ε ⊢ t₁ ≅ t₂))

  [Ind] : ∀ (c : CName) (d : DName c) (pars : Vec AST (arityC c)) (ixs : Vec AST (numIxC c)) (args : Vec AST (arityD c d)) (rhses : Vec AST (numCtors c)) →
    --------------------------------------------
    Redex (Sind c i (d ^ i [ pars ,, ixs ,, args ]) T rhses)


  [PropΠ] : ∀ T₁ T₂ (which : OpI ⁇℧Syn) →
    -------------------------------
    Redex ( ⁇or℧[ which ][ [x⦂ T₁ ]⟶ T₂ ])

  [Prop≡] : ∀ T t₁ t₂ (which : OpI ⁇℧Syn) →
    -------------------------------
    Redex ( ⁇or℧[ which ][ t₁ ≡[ T ] t₂ ])

  [PropInd] : ∀ T pars ixs (which : OpI ⁇℧Syn) {rhses} →
    -------------------------------
    Redex ( Sind c i ⁇or℧[ which ][ c ^ i [ pars ,, ixs ] ] T rhses )

  [CastBadHead] : ∀ (TH1 : OpI Ty) subs1 {TH2 : OpI Ty} {subs2} → ¬ (TH1 ≡p TH2) →
    Redex (⟨ ABT→AST (op TH1 ⦅ subs1 ⦆) ⇐ ABT→AST (op TH2 ⦅ subs2 ⦆) ⟩ t)

  [CastΠ] : ∀ T₁ T₂ T'₁ T'₂ t →
    Redex (⟨ [x⦂ T'₁ ]⟶ T'₂ ⇐ [x⦂ T₁ ]⟶ T₂ ⟩ t)

  [CastC] : ∀ c d pars1 pars2 ix1 ix2 args →
    Redex (⟨ c ^ i [ pars2 ,, ix2 ] ⇐ c ^ i [ pars1 ,, ix1 ] ⟩ ( d ^ i [ pars1 ,, ix1 ,, args ] ))

  [CastTyTy] : ∀ t →
    Redex (⟨ SType i ⇐ SType i ⟩ t)

  [CastFrom℧] : ∀ T →
    Redex (⟨ T ⇐ ℧[ SType i ] ⟩ t)

  [CastTo℧] :
    Redex (⟨ ℧[ SType i ] ⇐ T ⟩ t)

  [CastTo⁇] : ∀ t (h : OpI Ty) args →
    Redex (⟨ ⁇[ SType i ] ⇐ ABT→AST ((op h) ⦅ args ⦆) ⟩ t)

  [CastΠFrom⁇] : ∀ T₁ T₂ t i →
    Redex ( ⟨ [x⦂ T₁ ]⟶ T₂ ⇐ ⁇[ SType i ] ⟩ (STag i OΠ t) )

  [Cast≡From⁇] : ∀ T t₁ t₂ ε i →
    Redex ( ⟨ t₁ ≡[ T ] t₂ ⇐ ⁇[ SType i ] ⟩ (STag i O≡ (ε ⊢ ⁇[ ⁇[ SType i ] ] ≅ ⁇[ ⁇[ SType i ] ])) )

  [CastCFrom⁇] : ∀ (c : CName) i (d : DName c)  pars1 pars2 ix1 ix2 args →
    Redex ( ⟨ c ^ i [ pars2 ,, ix2 ] ⇐ ⁇[ SType i ] ⟩ (STag i (OC c i) (d ^ i [ pars1 ,, ix1 ,, args ])) )

  [CastTypeFrom⁇] : ∀ T i j →
    Redex ( ⟨ SType j ⇐ ⁇[ SType i ] ⟩ (STag i (OType j) T) )

  [CastEq] : ∀ T T' t₁ t₂ t'₁ t'₂ ε →
    Redex (⟨ t'₁ ≡[ T' ] t'₂ ⇐ t₁ ≡[ T ] t₂ ⟩ (ε ⊢ t₁ ≅ t₂))

-- Meed reductions
  [MeetTag] : ∀ h t₁ t₂ i →
    Redex (STag i h t₁ &[ ⁇[ SType i ] ] STag i h t₂)

  [MeetTagRedErr] : ∀ h₁ h₂ t₁ t₂ i → ¬ (h₁ ≡p h₂) →
    Redex (STag i h₁ t₁ &[ ⁇[ SType i ] ] STag i h₂ t₂)

  [MeetGradL] : ∀ which t T →
    Redex (⁇or℧[ which ][ T ] &[ T ] t)

  [MeetGradR] : ∀ which t T → --TODO conditions on T?
    Redex (t &[ T ] ⁇or℧[ which ][ T ] )

  [MeetErrIntro] : ∀ (h1 h2 : OpI Intro) args1 args2 T  → ¬ (h1 ≡p h2) →
    Redex (ABT→AST ((op h1) ⦅ args1 ⦆) &[ T ] ABT→AST ((op h2) ⦅ args2 ⦆))

  [MeetErrTy] : ∀ (h1 h2 : OpI Ty) args1 args2 i  → ¬ (h1 ≡p h2) →
    Redex (ABT→AST ((op h1) ⦅ args1 ⦆) &[ SType i ] ABT→AST ((op h2) ⦅ args2 ⦆))

  [MeetEq] : ∀ T T' t₁ t₂ t'₁ t'₂ i →
    Redex ((t₁ ≡[ T ] t₂) &[ SType i ] (t'₁ ≡[ T' ] t'₂))

  [MeetC] : ∀ (c : CName) pars1 pars2 ix1 ix2 i →
    Redex ( (c ^ i [ pars1 ,, ix1 ]) &[ SType i ] (c ^ i [ pars2 ,, ix2 ]))

  [MeetΠ] : ∀ T₁ T₂ T'₁ T'₂ i →
    Redex ( ([x⦂ T₁ ]⟶ T₂) &[ SType i ] ([x⦂ T'₁ ]⟶ T'₂))

  [MeetType] : ∀ i j →
   Redex (SType i &[ SType j ] SType i)

  [MeetD] : ∀ (c : CName) (d : DName c) param ix args1 args2 i →
    Redex ((d ^ i [ param ,, ix ,, args1 ]) &[ c ^ i [ param ,, ix ] ] (d ^ i [ param ,, ix ,, args2 ]))

  [MeetRefl] : ∀ T t₁ t₂ ε1 ε2 →
    Redex ( (ε1 ⊢ t₁ ≅ t₂) &[ t₁ ≡[ T ] t₂ ] (ε2 ⊢ t₁ ≅ t₂) )

  [MeetFun] : ∀ T₁ T₂ t t' →
    Redex ((λx⦂ T₁ ∙ t) &[ [x⦂ T₁ ]⟶ T₂ ] (λx⦂ T₁ ∙ t'))

open import Source.Sub
open import Substitution as ABTSub
open import GSubst as ABTSub
open import Source.Germ

iterCastArgs : ∀ {m n p} (pars1 pars2 : Vec AST n) (ix1 ix2 : Vec AST m) (argTypes : Vec AST p) (args : Vec AST p) → Vec AST p
iterCastArgs pars1 pars2 ix1 ix2 [] [] = []
iterCastArgs pars1 pars2 ix1 ix2 (T ∷ Ts) (arg ∷ args) with ret ← iterCastArgs pars1 pars2 ix1 ix2 Ts args
    = (⟨ [ subFirstN (pars2 V.++ ix2 V.++ ret) /x⃗] T ⇐ [ subFirstN (pars1 V.++ ix1 V.++ args) /x⃗] T ⟩ arg) ∷ ret

iterMeet : ∀ {n} (tele : Vec AST n ) → Vec AST n → Vec AST n → Vec AST n
iterMeet {zero} [] [] [] = []
iterMeet {suc n} (T ∷ tl) (x ∷ xs) (y ∷ ys)
  = ((⟨ [ subFirstN recCall /x⃗] T ⇐  [ subFirstN xs /x⃗] T ⟩ x) &[ [ subFirstN recCall /x⃗] T ] (⟨ [ subFirstN recCall /x⃗] T ⇐ [ subFirstN ys /x⃗] T ⟩ y)) ∷ recCall
  where
    recCall = iterMeet tl xs ys

--TODO check right order

reduce : ∀ {t} → Redex t → AST
reduce {.((λx⦂ _ ∙ t) $ t₂)} ([β] t t₂) = [ t₂ /x] t
reduce {.(SJ T t₁ t₂ t (ε ⊢ t₁ ≅ t₂))} ([J] T t₁ t₂ t ε) = ⟨ [ t₂ /x] T ⇐  [ ε /x] T ⟩ (⟨  [ ε /x] T ⇐  [ t₁ /x] T ⟩ t)
reduce {.(Sind c _ (d ^ _ [ pars ,, ixs ,, args ]) _ rhses)} ([Ind] c d pars ixs args rhses) = [ subFirstN (ixs V.++ args) /x⃗] (lookup d rhses)
reduce {.(⁇or℧[ _ ][ [x⦂ _ ]⟶ _ ])} ([PropΠ] T₁ T₂ ⁇or℧) = λx⦂ ⁇or℧[ ⁇or℧ ][ T₁ ] ∙ ⁇or℧[ ⁇or℧ ][ T₂ ]
reduce {.(Sind _ _ ⁇or℧[ ⁇or℧ ][ _ ^ _ [ pars ,, ixs ] ] T _)} ([PropInd] {c = c} {i = i} T pars ixs ⁇or℧) = ⁇or℧[ ⁇or℧ ][ [ ⁇or℧[ ⁇or℧ ][ c ^ i [ pars ,, ixs ] ] /x] T ]
reduce {.(⟨ ABT→AST (op TH1 ⦅ subs1 ⦆) ⇐ ABT→AST (op TH2 ⦅ _ ⦆) ⟩ _)} ([CastBadHead]  TH1 subs1 {TH2 = TH2} x ) = ℧[ ABT→AST (op TH1 ⦅ subs1 ⦆) ]
-- TODO check if need weakening
reduce {.(⟨ [x⦂ T'₁ ]⟶ T'₂ ⇐ [x⦂ T₁ ]⟶ T₂ ⟩ t)} ([CastΠ] T₁ T₂ T'₁ T'₂ t) = λx⦂ T'₁ ∙ (⟨ T₂ ⇐  [ (⟨ T₁ ⇐ T'₁ ⟩ x0) /x] T₂ ⟩ (t $ (⟨ T₁ ⇐ T'₁ ⟩ x0)))
reduce {.(⟨ c ^ _ [ pars2 ,, ix2 ] ⇐ c ^ _ [ pars1 ,, ix1 ] ⟩ (d ^ _ [ pars1 ,, ix1 ,, args ]))} ([CastC] {i = i} c d pars1 pars2 ix1 ix2 args) = d ^ i [ pars2 ,, ix2 ,, iterCastArgs pars1 pars2 ix1 ix2 (argTypes d) args ]
reduce {.(⟨ SType _ ⇐ SType _ ⟩ t)} ([CastTyTy] t) = t
reduce {.(⟨ T ⇐ ℧[ SType _ ] ⟩ _)} ([CastFrom℧] T) = ℧[ T ]
reduce {.(⟨ ℧[ SType _ ] ⇐ _ ⟩ _)} ([CastTo℧] {i = i}) = ℧[ ℧[ SType i ] ]
reduce {.(⟨ ⁇[ SType _ ] ⇐ ABT→AST (op h ⦅ args ⦆) ⟩ t)} ([CastTo⁇] {i = i} t h args) = STag i h (⟨ Germ h i ⇐ ABT→AST (op h ⦅ args ⦆) ⟩ t)
reduce {.(⁇or℧[ ⁇or℧ ][ t₁ ≡[ T ] t₂ ])} ([Prop≡] T t₁ t₂ ⁇or℧) = (t₁ &[ T ] t₁) ⊢ t₁ ≅ t₂
reduce {.(⟨ [x⦂ T₁ ]⟶ T₂ ⇐ ⁇[ SType i ] ⟩ STag i OΠ t)} ([CastΠFrom⁇] T₁ T₂ t i) = λx⦂ T₁ ∙ (⟨ T₂ ⇐ ⁇[ SType i ] ⟩ (t $ (⟨ ⁇[ SType i ] ⇐ T₁ ⟩ x0)))
reduce {.(⟨ t₁ ≡[ T ] t₂ ⇐ ⁇[ SType i ] ⟩ STag i O≡ (ε ⊢ ⁇[ ⁇[ SType i ] ] ≅ ⁇[ ⁇[ SType i ] ]))} ([Cast≡From⁇] T t₁ t₂ ε i) = (⟨ T ⇐ ⁇[ SType i ] ⟩ ε) ⊢ t₁ ≅ t₂
reduce {.(⟨ c ^ i [ pars2 ,, ix2 ] ⇐ ⁇[ SType i ] ⟩ STag i (OC c i) (d ^ i [ pars1 ,, ix1 ,, args ]))} ([CastCFrom⁇] c i d pars1 pars2 ix1 ix2 args) =
  ⟨ c ^ i [ pars2 ,, ix2 ] ⇐ c ^ i [ pars1 ,, ix1 ] ⟩ (d ^ i [ pars1 ,, ix1 ,, args ])
reduce {.(⟨ SType j ⇐ ⁇[ SType i ] ⟩ STag i (OType j) T)} ([CastTypeFrom⁇] T i j) = T
reduce {.(STag i h t₁ &[ ⁇[ SType i ] ] STag i h t₂)} ([MeetTag] h t₁ t₂ i) = STag i h (t₁ &[ Germ h i ] t₂)
reduce {.(STag i h₁ t₁ &[ ⁇[ SType i ] ] STag i h₂ t₂)} ([MeetTagRedErr] h₁ h₂ t₁ t₂ i x) = ℧[ ⁇[ SType i ] ]
reduce {.(⁇or℧[ O⁇ ][ T ] &[ T ] t)} ([MeetGradL] O⁇ t T) = t
reduce {.(⁇or℧[ O℧ ][ T ] &[ T ] t)} ([MeetGradL] O℧ t T) = ℧[ T ]
reduce {.(t &[ T ] ⁇or℧[ O⁇ ][ T ])} ([MeetGradR] O⁇ t T) = t
reduce {.(t &[ T ] ⁇or℧[ O℧ ][ T ])} ([MeetGradR] O℧ t T) = ℧[ T ]
reduce {.(ABT→AST (op h1 ⦅ args1 ⦆) &[ T ] ABT→AST (op h2 ⦅ args2 ⦆))} ([MeetErrIntro] h1 h2 args1 args2 T x) = ℧[ T ]
reduce {.(ABT→AST (op h1 ⦅ args1 ⦆) &[ SType i ] ABT→AST (op h2 ⦅ args2 ⦆))} ([MeetErrTy] h1 h2 args1 args2 i x) = ℧[ SType i ]
reduce {.((λx⦂ T₁ ∙ t) &[ [x⦂ T₁ ]⟶ T₂ ] (λx⦂ T₁ ∙ t'))} ([MeetFun] T₁ T₂ t t') = λx⦂ T₁ ∙ ((t $ x0) &[ T₂ ] (t' $ x0))
reduce {.((t₁ ≡[ T ] t₂) &[ SType i ] (t'₁ ≡[ T' ] t'₂))} ([MeetEq] T T' t₁ t₂ t'₁ t'₂ i) =
  ( (⟨ T &[ SType i ] T' ⇐ T ⟩ t₁)  &[ T &[ SType i ] T' ] (⟨ T &[ SType i ] T' ⇐ T' ⟩ t'₁)) ≡[ T &[ SType i ] T' ] ( (⟨ T &[ SType i ] T' ⇐ T ⟩ t₂) &[ T &[ SType i ] T' ] (⟨ T &[ SType i ] T' ⇐ T' ⟩ t'₂))
reduce {.((c ^ i [ pars1 ,, ix1 ]) &[ SType i ] (c ^ i [ pars2 ,, ix2 ]))} ([MeetC] c pars1 pars2 ix1 ix2 i) = SC c i (iterMeet (paramTypes c V.++ indexTypes c) (pars1 V.++ ix1) (pars2 V.++ ix2))
reduce {.(([x⦂ T₁ ]⟶ T₂) &[ SType i ] ([x⦂ T'₁ ]⟶ T'₂))} ([MeetΠ] T₁ T₂ T'₁ T'₂ i) = [x⦂ T₁ &[ SType i ] T'₁ ]⟶ (([ ⟨ T₁ &[ SType i ] T'₁ ⇐ T₁ ⟩ x0 /x] T₂) &[ SType i ] ( [ ⟨ T₁ &[ SType i ] T'₁ ⇐ T'₁ ⟩ x0 /x] T'₂))
reduce {.(SType i &[ SType j ] SType i)} ([MeetType] i j) = SType i
--TODO sub in arg types for params
reduce {.((d ^ i [ param ,, ix ,, args1 ]) &[ c ^ i [ param ,, ix ] ] (d ^ i [ param ,, ix ,, args2 ]))} ([MeetD] c d param ix args1 args2 i)
  = d ^ i [ param ,, ix ,, iterMeet (argTypes d) args1 args2 ]
reduce {.((ε1 ⊢ t₁ ≅ t₂) &[ t₁ ≡[ T ] t₂ ] (ε2 ⊢ t₁ ≅ t₂))} ([MeetRefl] T t₁ t₂ ε1 ε2) = (ε1 &[ T ] ε2) ⊢ t₁ ≅ t₂
reduce {.(⟨ t'₁ ≡[ T' ] t'₂ ⇐ t₁ ≡[ T ] t₂ ⟩ (ε ⊢ t₁ ≅ t₂))} ([CastEq] T T' t₁ t₂ t'₁ t'₂ ε) = ((⟨ T' ⇐ T ⟩ ε) &[ T' ] (t'₁ &[ T' ] t'₂)) ⊢ t'₁ ≅ t'₂
--TODO approx
-- reduce {.(⟨ ABT→AST (op h ⦅ args ⦆) ⇐ ⁇[ SType _ ] ⟩ STag h t)} ([CastFrom⁇] t h args) = {!!}

data _↝_ : AST → AST → Set where
  step : ∀ {t} → (red : Redex t) → t ↝ reduce red

Value : Set
Value = AST / _↝_

eval : AST → Value
eval t = [ t ]

data _≡↝_ : AST → AST → Set where
  quotRedex : ∀ {t t'} → eval t ≡ eval t' → t ≡↝ t'


instance
 defeqRefl : ∀ {t} → t ≡↝ t
 defeqRefl = quotRedex refl

germSub : ∀ {h i sub} → [ sub /x⃗] (Germ h i) ≡p Germ h i
teleGermSub : ∀ {n sub} (v : Vec AST n) → V.map ([ sub /x⃗]) (TeleGerm v) ≡p TeleGerm v
germSub {OType x} = reflp
germSub {OΠ} = reflp
germSub {OC c j} {i = i}  = pCong (λ x → SC c i x) (teleGermSub (paramTypes c V.++ indexTypes c))
germSub {O≡} = reflp

teleGermSub [] = reflp
teleGermSub {suc n} {sub} (x ∷ v) rewrite teleGermSub {n} {sub} v  = pCong {x = (extN n sub ⨟ subFirstN (TeleGerm v) )} {y = subFirstN (TeleGerm v) } (λ sub → ⁇[ ([ sub /x⃗] x) ] ∷ TeleGerm v) {!reflp!}


-- iterMeetMap : ∀ {n sub} (t : Vec AST n) v1 v2 → V.map [ sub /x⃗] (iterMeet t v1 v2) ≡p iterMeet t (V.map [ sub /x⃗] v1) (V.map [ sub /x⃗] v2)
-- iterMeetMap [] [] [] = reflp
-- iterMeetMap (x ∷ t) (x₁ ∷ v1) (x₂ ∷ v2)  = {!!}
