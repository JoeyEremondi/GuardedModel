-- Implementation of the meet on codes, assuming we have meet, cast, etc. for smaller types


open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Equality
open import Inductives
open import GuardedAlgebra
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude

open import ApproxExact
open import InductiveCodes
open import CodeSize
open import WMuEq
open import Ord

open import CastComp.Interface

module CastComp.CodeMeet {{_ : DataTypes}} {{_ : DataGerms}} {{_ : InductiveCodes}} {{_ : DataGermsSmaller}}
    {ℓ} (cSize : Ord) (vSize : Ord) {{_ : SmallerCastMeet ℓ cSize vSize}}

  where

open import Code
open import Head
open import Util



codeMeet : ∀ {{_ : Æ}} {h1 h2}
  → (c1 c2 : ℂ ℓ )
  → IndWF c1 → IndWF c2
  → HeadMatchView h1 h2
  → h1 ≡p codeHead c1
  → h2 ≡p codeHead c2
  → (csize (codePairSize c1 c2) ≡p cSize)
  → (OZ ≡p vSize)
  → (ℂ ℓ)
-- Error cases: the meet is ℧ if either argument is ℧
-- or the heads don't match
codeMeet _ c2 wf1 wf2 (H℧L reflp) eq1 eq2 reflp reflp = C℧
codeMeet c1 _ wf1 wf2 (H℧R reflp) eq1 eq2 reflp reflp = C℧
codeMeet c1 c2 wf1 wf2 (HNeq x) eq1 eq2 reflp reflp = C℧
-- Meet of anything with ⁇ is that thing
codeMeet _ c2 wf1 wf2 (H⁇L reflp x₁) eq1 eq2 reflp reflp = c2
codeMeet c1 _ wf1 wf2 (H⁇R reflp) eq1 eq2 reflp reflp = c1
-- Otherwise, we have two codes with the same head, so we take the meet of the parts
-- after performing the required casts
codeMeet (CodeModule.CΠ c1 cod) (CodeModule.CΠ c2 cod₁) wf1 wf2 (HEq {h1 = HΠ} reflp) eq1 eq2 reflp reflp = {!!}
codeMeet (CodeModule.CΣ c1 cod) (CodeModule.CΣ c2 cod₁) wf1 wf2 (HEq {h1 = HΣ} reflp) eq1 eq2 reflp reflp = {!!}
codeMeet (CodeModule.C≡ c1 x y) (CodeModule.C≡ c2 x₁ y₁) wf1 wf2 (HEq {h1 = H≅} reflp) eq1 eq2 reflp reflp = {!!}
codeMeet CodeModule.C𝟙 CodeModule.C𝟙 wf1 wf2 (HEq {h1 = H𝟙} reflp) eq1 eq2 reflp reflp = {!!}
codeMeet CodeModule.C𝟘 CodeModule.C𝟘 wf1 wf2 (HEq {h1 = H𝟘} reflp) eq1 eq2 reflp reflp = {!!}
codeMeet CodeModule.CType CodeModule.CType wf1 wf2 (HEq {h1 = HType} reflp) eq1 eq2 reflp reflp = {!!}
codeMeet (CodeModule.Cμ tyCtor c1 D x) (CodeModule.Cμ tyCtor₁ c2 D₁ x₁) wf1 wf2 (HEq {h1 = HCtor x₂} reflp) eq1 eq2 reflp reflp = {!!}
