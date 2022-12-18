{-# OPTIONS --rewriting #-}
open import Source.SyntaxParams
open import Source.Tele {{CastCalc}}

open import Cubical.Data.Equality hiding (Sub)

module Source.SubstReduction  {{ind : Inductives}} {{_ : IndParams}}   where

instance cc : Language
cc = CastCalc

open import Source.SubstRedex

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
open import Source.Redex


reductionPreservesSubst :  ∀ {t} sub → (red : Redex t) →  [ sub /x⃗] (reduce red) ≡p reduce (substRedex sub red)
reductionPreservesSubst sub ([β] t t₂) =  reflp -- reflp
reductionPreservesSubst sub ([J] T t₁ t₂ t ε) = reflp -- reflp
reductionPreservesSubst sub ([Ind] c d pars ixs args rhses) = {!reflp!}
reductionPreservesSubst sub ([PropΠ] T₁ T₂ which) = reflp -- reflp
reductionPreservesSubst sub ([Prop≡] T t₁ t₂ which) = reflp
reductionPreservesSubst sub ([PropInd] T pars ixs which) = {!reflp!} --reflp
reductionPreservesSubst sub ([CastBadHead] TH1 subs1 x) = reflp
reductionPreservesSubst sub ([CastΠ] T₁ T₂ T'₁ T'₂ t) =  {!reflp!}
reductionPreservesSubst sub ([CastC] c d pars1 pars2 ix1 ix2 args) = {!reflp!}
reductionPreservesSubst sub ([CastTyTy] t) = reflp
reductionPreservesSubst sub ([CastFrom℧] T) = reflp
reductionPreservesSubst sub [CastTo℧] = reflp
reductionPreservesSubst sub ([CastTo⁇] t h args) = {!reflp!}
reductionPreservesSubst sub ([CastΠFrom⁇] T₁ T₂ t i) = {!reflp!}
reductionPreservesSubst sub ([Cast≡From⁇] T t₁ t₂ ε i) = reflp
reductionPreservesSubst sub ([CastCFrom⁇] c i d pars1 pars2 ix1 ix2 args) = reflp
reductionPreservesSubst sub ([CastTypeFrom⁇] T i j) = reflp
reductionPreservesSubst sub ([CastEq] T T' t₁ t₂ t'₁ t'₂ ε) = reflp
reductionPreservesSubst sub ([MeetTag] h t₁ t₂ i) = {!reflp!}
reductionPreservesSubst sub ([MeetTagRedErr] h₁ h₂ t₁ t₂ i x) = reflp
reductionPreservesSubst sub ([MeetGradL] O⁇ t T) = reflp
reductionPreservesSubst sub ([MeetGradL] O℧ t T) = reflp
reductionPreservesSubst sub ([MeetGradR] O⁇ t T) = reflp
reductionPreservesSubst sub ([MeetGradR] O℧ t T) = reflp
reductionPreservesSubst sub ([MeetErrIntro] h1 h2 args1 args2 T x) = reflp
reductionPreservesSubst sub ([MeetErrTy] h1 h2 args1 args2 i x) = reflp
reductionPreservesSubst sub ([MeetEq] T T' t₁ t₂ t'₁ t'₂ i) = reflp
reductionPreservesSubst sub ([MeetC] c pars1 pars2 ix1 ix2 i) = {!reflp!}
reductionPreservesSubst sub ([MeetΠ] T₁ T₂ T'₁ T'₂ i) = {!reflp!}
reductionPreservesSubst sub ([MeetType] i j) = reflp
reductionPreservesSubst sub ([MeetD] c d param ix args1 args2 i) = {!reflp!}
reductionPreservesSubst sub ([MeetRefl] T t₁ t₂ ε1 ε2) = reflp
reductionPreservesSubst sub ([MeetFun] T₁ T₂ t t') = reflp
