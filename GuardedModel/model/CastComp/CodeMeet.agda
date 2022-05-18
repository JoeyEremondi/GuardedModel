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
  → (view : HeadMatchView h1 h2)
  → (eq1 : h1 ≡p codeHead c1)
  → (eq2 : h2 ≡p codeHead c2)
  → (csize (codePairSize c1 c2 {view} {eq1} {eq2}) ≡p cSize)
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
-- First: trivial cases, where both types are identical
codeMeet CodeModule.C𝟙 CodeModule.C𝟙 wf1 wf2 (HEq {h1 = H𝟙} reflp) eq1 eq2 reflp reflp = C𝟙
codeMeet CodeModule.C𝟘 CodeModule.C𝟘 wf1 wf2 (HEq {h1 = H𝟘} reflp) eq1 eq2 reflp reflp = C𝟘
codeMeet CodeModule.CType CodeModule.CType wf1 wf2 (HEq {h1 = HType} reflp) eq1 eq2 reflp reflp = {!!}
codeMeet (CodeModule.CΠ c1 cod) (CodeModule.CΠ c2 cod₁) wf1 wf2 (HEq {h1 = HΠ} reflp) eq1 eq2 reflp reflp = {!!}
codeMeet (CodeModule.CΣ c1 cod) (CodeModule.CΣ c2 cod₁) wf1 wf2 (HEq {h1 = HΣ} reflp) eq1 eq2 reflp reflp = {!!}
codeMeet (CodeModule.C≡ c1 x y) (CodeModule.C≡ c2 x₁ y₁) wf1 wf2 (HEq {h1 = H≅} reflp) eq1 eq2 reflp reflp = {!!}
codeMeet (CodeModule.Cμ tyCtor c1 D x) (CodeModule.Cμ tyCtor₁ c2 D₁ x₁) wf1 wf2 (HEq {h1 = HCtor x₂} reflp) eq1 eq2 reflp reflp = {!!}



--     -- Otherwise, we have two codes with the same head
--     -- Trivial cases with no arguments: both inputs are identical
--     codeMeet (C𝟙 |wf| wf1) (C𝟙 |wf| wf2) reflp reflp | HStatic H𝟙  | .(HStatic H𝟙)  | HEq reflp = C𝟙 |wf| IWF𝟙
--     codeMeet (C𝟘 |wf| wf1) (C𝟘 |wf| wf2) reflp reflp | HStatic H𝟘  | .(HStatic H𝟘)  | HEq reflp = C𝟘 |wf| IWF𝟘
--     codeMeet (CType {{suc<}} |wf| wf1) (CType |wf| wf2) reflp reflp | HStatic HType  | .(HStatic HType)  | HEq reflp = CType {{_}} {{_}} {{suc<}} |wf| IWFType
--     codeMeet (CΠ dom1 cod1 |wf| (IWFΠ domwf1 codwf1)) (CΠ dom2 cod2 |wf| (IWFΠ domwf2 codwf2)) reflp reflp | HStatic HΠ  | .(HStatic HΠ)  | HEq reflp
--       =
--         let
--           dom12 = (dom1 |wf| domwf1) ⊓ (dom2 |wf| domwf2)
--                         By ≤o-sucMono omax-≤L
--           cod12 : (x : wfApproxEl dom12) → ℂwf ℓ
--           cod12 x12 =
--             let
--               x1 = [ Approx ]⟨ dom1 |wf| domwf1 ⇐ dom12 ⟩ x12 By ≤o-sucMono omax-≤L
--               x2 = [ Approx ]⟨ dom2 |wf| domwf2 ⇐ dom12 ⟩ x12 By {!!}
--             in
--               (cod1 (fromL x1) |wf| codwf1 _) ⊓ cod2 (fromL x2) |wf| codwf2 _
--                       By {!!}
--         in CΠ
--           (code dom12)
--           {!λ x → !}
--         |wf| {!!}
--     codeMeet (CΣ c1 cod |wf| wf1) (CΣ c2 cod₁ |wf| wf2) reflp reflp | HStatic HΣ  | .(HStatic HΣ)  | HEq reflp = {!!}
--     codeMeet (C≡ c1 x y |wf| wf1) (C≡ c2 x₁ y₁ |wf| wf2) reflp reflp | HStatic H≅  | .(HStatic H≅)  | HEq reflp = {!!}
--     codeMeet (Cμ tyCtor c1 D x |wf| wf1) (Cμ tyCtor₁ c2 D₁ x₁ |wf| wf2) reflp reflp | HStatic (HCtor x₂)  | .(HStatic (HCtor x₂))  | HEq reflp = {!!}
