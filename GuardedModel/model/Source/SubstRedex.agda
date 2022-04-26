{-# OPTIONS --rewriting #-}
open import Source.SyntaxParams
open import Source.Tele {{CastCalc}}

open import Cubical.Data.Equality hiding (Sub)

module Source.SubstRedex  {{ind : Inductives}} {{_ : IndParams}}   where

open import DecPEq
open import Cubical.Data.Nat
open import Source.Syntax {{CastCalc}}
open import Cubical.Data.Vec as V
open import Cubical.Data.Sum
open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary
open import Cubical.Data.Bool

open import Syntax using (Sig ; ν ;  ■ )

open import Cubical.Data.List hiding ([_])

open import Source.SubProperties
open import Source.Sub
open import Source.Redex



substRedex : ∀ {t} sub → Redex t →  Redex ([ sub /x⃗] t)
substRedex sub ([β] t t₂) = [β] _ _
substRedex sub ([J] T t₁ t₂ t ε) = [J] _ _ _ _ _
substRedex sub ([PropΠ] T₁ T₂ which) = [PropΠ] _ _ _
substRedex sub ([Ind] c d pars ixs args rhses) = [Ind] c d (V.map [ sub /x⃗] pars) (V.map [ sub /x⃗] ixs) (V.map [ sub /x⃗] args) _
substRedex sub ([Prop≡] T t₁ t₂ which) = [Prop≡] _ _ _ _
substRedex sub ([PropInd] T pars ixs which) = [PropInd] _ (V.map [ sub /x⃗] pars) (V.map [ sub /x⃗] ixs) which
substRedex sub ([CastBadHead] TH1 subs1 {TH2} x) = [CastBadHead] TH1 _ {TH2} x
substRedex sub ([CastΠ] T₁ T₂ T'₁ T'₂ t) = [CastΠ] _ _ _ _ _
substRedex sub ([CastC] c d pars1 pars2 ix1 ix2 args) = [CastC] c d (V.map [ sub /x⃗] pars1) (V.map [ sub /x⃗] pars2) (V.map [ sub /x⃗] ix1) (V.map [ sub /x⃗] ix2) (V.map [ sub /x⃗] args)
substRedex sub ([CastTyTy] t) = [CastTyTy] _
substRedex sub ([CastFrom℧] T) = [CastFrom℧] _
substRedex sub [CastTo℧] = [CastTo℧]
substRedex sub ([CastTo⁇] t h args) = [CastTo⁇] _ h _
substRedex sub ([CastΠFrom⁇] T₁ T₂ t i) = [CastΠFrom⁇] _ _ _ _
substRedex sub ([Cast≡From⁇] T t₁ t₂ ε i) = [Cast≡From⁇] _ _ _ _ _
substRedex sub ([CastCFrom⁇] c i d pars1 pars2 ix1 ix2 args) = [CastCFrom⁇] c i d (V.map [ sub /x⃗] pars1) (V.map [ sub /x⃗] pars2) (V.map [ sub /x⃗] ix1) (V.map [ sub /x⃗] ix2) (V.map [ sub /x⃗] args)
substRedex sub ([CastTypeFrom⁇] T i j) = [CastTypeFrom⁇] _ _ _
substRedex sub ([CastEq] T T' t₁ t₂ t'₁ t'₂ ε) = [CastEq] _ _ _ _ _ _ _
substRedex sub ([MeetTag] h t₁ t₂ i) = [MeetTag] _ _ _ _
substRedex sub ([MeetTagRedErr] h₁ h₂ t₁ t₂ i x) = [MeetTagRedErr] h₁ h₂ _ _ _ x
substRedex sub ([MeetGradL] which t T) =  [MeetGradL] _ _ _
substRedex sub ([MeetGradR] which t T) =  [MeetGradR] _ _ _
substRedex sub ([MeetErrIntro] h1 h2 args1 args2 T x) = [MeetErrIntro] h1 h2 _ _ _ x
substRedex sub ([MeetErrTy] h1 h2 args1 args2 i x) = [MeetErrTy] h1 h2 _ _ _ x
substRedex sub ([MeetEq] T T' t₁ t₂ t'₁ t'₂ i) = [MeetEq] _ _ _ _ _ _ _
substRedex sub ([MeetC] c pars1 pars2 ix1 ix2 i) = [MeetC] _ (V.map [ sub /x⃗] pars1) (V.map [ sub /x⃗] pars2) (V.map [ sub /x⃗] ix1) (V.map [ sub /x⃗] ix2) _
substRedex sub ([MeetΠ] T₁ T₂ T'₁ T'₂ i) = [MeetΠ] _ _ _ _ _
substRedex sub ([MeetType] i j) = [MeetType] i j
substRedex sub ([MeetD] c d param ix args1 args2 i) = [MeetD] _ _ (V.map [ sub /x⃗] param) (V.map [ sub /x⃗] ix) (V.map [ sub /x⃗] args1) (V.map [ sub /x⃗] args2) _
substRedex sub ([MeetRefl] T t₁ t₂ ε1 ε2) = [MeetRefl] _ _ _ _ _
substRedex sub ([MeetFun] T₁ T₂ t t') = [MeetFun] _ _ _ _
