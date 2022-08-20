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
-- open import CodePair
open import WMuEq
open import Ord

open import CastComp.Interface

module CastComp.CodeMeet {{dt : DataTypes}} {{dg : DataGerms}} {{ic : InductiveCodes}} {{dgs : DataGermsSmaller}}
    {ℓ} (cSize : Ord) (vSize : Ord) (scm : SmallerCastMeet ℓ cSize vSize)

  where

open import Code
open import Head
open import Util


open SmallerCastMeet scm


{-# DISPLAY SmallerCastMeet._⊓_By_  = _⊓_By_  #-}
{-# DISPLAY SmallerCastMeet._∋_⊓_By_  = _∋_⊓_By_  #-}

codeMeet : ∀ {{_ : Æ}} {h1 h2}
  → (c1 c2 : ℂ ℓ )
  → (view : HeadMatchView h1 h2)
  → (eq1 : h1 ≡p codeHead c1)
  → (eq2 : h2 ≡p codeHead c2)
  → (omax (codeSize c1) ( codeSize c2) ≡p cSize)
  → (OZ ≡p vSize)
  → (ℂ ℓ)
-- Error cases: the meet is ℧ if either argument is ℧
-- or the heads don't match
codeMeet _ c2  (H℧L reflp) eq1 eq2 reflp reflp = C℧
codeMeet c1 _  (H℧R reflp) eq1 eq2 reflp reflp = C℧
codeMeet c1 c2  (HNeq x) eq1 eq2 reflp reflp = C℧
-- Meet of anything with ⁇ is that thing
codeMeet _ c2  (H⁇L reflp x₁) eq1 eq2 reflp reflp = c2
codeMeet c1 _  (H⁇R reflp) eq1 eq2 reflp reflp = c1
-- Otherwise, we have two codes with the same head, so we take the meet of the parts
-- after performing the required casts
-- First: trivial cases, where both types are identical
codeMeet C𝟙 C𝟙  (HEq {h1 = H𝟙} reflp) eq1 eq2 reflp reflp = C𝟙
codeMeet C𝟘 C𝟘  (HEq {h1 = H𝟘} reflp) eq1 eq2 reflp reflp = C𝟘
codeMeet (CType {{inst}}) CType  (HEq {h1 = HType} reflp) eq1 eq2 reflp reflp = CType {{inst = inst}}
-- Pi and Sigma types: we take the meet of the domains, then produce a codomain that takes the meet
-- after casting the argument to the appropriate type
codeMeet (CΠ dom1 cod1) (CΠ dom2 cod2)  (HEq {h1 = HΠ} reflp) eq1 eq2 reflp reflp
        = let
          dom12 = dom1 ⊓ dom2 By hide {arg = omax∞-<Ls}
          cod12 : (x : ApproxEl dom12) → ℂ ℓ
          cod12 x12 =
            let (x1 , x2) = fromL ([ Approx ]⟨ dom1 , dom2 ⇐⊓By hide {arg = omax-sucMono (omax-mono omax-≤L omax-≤L)} ⟩ {!!})
            in  (cod1 x1 ) ⊓ cod2 x2
                      By hide {arg = omax-sucMono (omax-mono
                        ( ≤o-cocone {{æ = Approx}} _ _ (omax∞-self _)
                          ≤⨟ omax-≤R)
                        (≤o-cocone {{æ = Approx}} _ _ (omax∞-self _)
                         ≤⨟ omax-≤R))}
        in CΠ dom12 cod12
codeMeet (CΣ dom1 cod1) (CΣ dom2 cod2)  (HEq {h1 = HΣ} reflp) eq1 eq2 reflp reflp
        = let
          dom12 = dom1 ⊓ dom2
                        By (hide {arg =
                          omax-strictMono {o1 = codeSize dom1} {o2 = codeSize dom2} {o1' = O↑ (omax (omax∞ (codeSize dom1)) _)}
                          (≤o-sucMono (omax∞-self (codeSize dom1) ≤⨟ omax-≤L))
                          (≤o-sucMono (omax∞-self (codeSize dom2) ≤⨟ omax-≤L )) })
          cod12 : (x : ApproxEl dom12) → ℂ ℓ
          cod12 x12 =
            let
              x1 = [ Approx ]⟨ dom1 ⇐ dom12 ⟩ x12
                By hide {arg = omax-sucMono (
                  (omax-monoL {o2 = codeSize dom1} ((dom1 ⊓Size dom2 By hide)  ))
                  ≤⨟ omax-assocR (codeSize dom1) (codeSize dom2) (codeSize dom1)
                  ≤⨟ omax-monoR {o1 = codeSize dom1} (omax-commut (codeSize dom2) (codeSize dom1))
                  ≤⨟ omax-assocL (codeSize dom1) (codeSize dom1) (codeSize dom2)
                  -- ≤⨟ omax-mono (omax-mono (omax∞-self (codeSize dom1)) (omax∞-self (codeSize dom1))) ((omax∞-self (codeSize dom2)))
                  ≤⨟ omax-mono (omax∞-idem∞ (codeSize dom1)) (omax∞-self (codeSize dom2)) -- omax-monoL {o2 = omax∞ (codeSize dom2)} (omax∞-idem (codeSize dom1))
                  ≤⨟ omax-mono {o1 = (omax∞ (codeSize dom1)) }{o2 =  (omax∞ (codeSize dom2))} {o1' = omax (omax∞ (codeSize dom1)) (OLim {{æ = Approx}} dom1 (λ x → omax∞ (codeSize (cod1 x))))}
                    (omax-≤L {o2 = (OLim {{æ = Approx}} dom1 (λ x → omax∞ (codeSize (cod1 x))))})
                    (omax-≤L {o2 = (OLim {{æ = Approx}} dom2 (λ x → omax∞ (codeSize (cod2 x))))})
                  )} -- [ Approx ]⟨ dom1 ⇐ dom12 ⟩ x12 By ≤o-sucMono omax-≤L
              x2 = [ Approx ]⟨ dom2 ⇐ dom12 ⟩ x12
                By hide {arg = omax-sucMono (
                  omax-monoL {o2 = codeSize dom2} (dom1 ⊓Size dom2 By hide)
                  ≤⨟ omax-assocR (codeSize dom1) (codeSize dom2) (codeSize dom2)
                  ≤⨟ omax-mono (omax∞-self (codeSize dom1)) (omax∞-idem∞ (codeSize dom2)) --omax-monoR {o1 = codeSize dom1} (omax-mono (omax∞-self (codeSize dom2)) (omax∞-self (codeSize dom2)))
                  ≤⨟ omax-mono {o1 = (omax∞ (codeSize dom1)) }{o2 =  (omax∞ (codeSize dom2))} {o1' = omax (omax∞ (codeSize dom1)) (OLim {{æ = Approx}} dom1 (λ x → omax∞ (codeSize (cod1 x))))}
                    (omax-≤L {o2 = (OLim {{æ = Approx}} dom1 (λ x → omax∞ (codeSize (cod1 x))))})
                    (omax-≤L {o2 = (OLim {{æ = Approx}} dom2 (λ x → omax∞ (codeSize (cod2 x))))})
                  )} -- [ Approx ]⟨ dom1 ⇐ dom12 ⟩ x12 By ≤o-sucMono omax-≤L
            in  (cod1 (fromL x1) ) ⊓ cod2 (fromL x2)
                      By hide {arg = omax-sucMono (omax-mono
                        ( ≤o-cocone {{æ = Approx}} _ _ (omax∞-self _)
                          ≤⨟ omax-≤R)
                        (≤o-cocone {{æ = Approx}} _ _ (omax∞-self _)
                         ≤⨟ omax-≤R))}
        in CΣ dom12 cod12
codeMeet (C≡ c1 x1 y1) (C≡ c2 x2 y2)  (HEq {h1 = H≅} reflp) eq1 eq2 reflp reflp
  = let
      c12 = c1 ⊓ c2 By hide {arg =
        omax-sucMono (omax-mono
          (omax∞-self (codeSize c1) ≤⨟ omax-≤L)
          (omax∞-self (codeSize c2) ≤⨟ omax-≤L))}
      lt1 =
          omax-sucMono
          (omax-monoR (c1 ⊓Size c2 By hide)
          ≤⨟ omax-assocL (codeSize c1) (codeSize c1) (codeSize c2)
          ≤⨟ omax-mono (omax∞-idem∞ (codeSize c1)) (omax∞-self (codeSize c2))
          ≤⨟ omax-mono omax-≤L omax-≤L)
      lt2 =
        omax-sucMono (
          omax-monoR (c1 ⊓Size c2 By hide)
          ≤⨟ omax-monoR (omax-commut _ _)
          ≤⨟ omax-assocL (codeSize c2) (codeSize c2) (codeSize c1)
          ≤⨟ omax-mono (omax∞-idem∞ (codeSize c2)) (omax∞-self (codeSize c1))
          ≤⨟ omax-commut _ _
          ≤⨟ omax-mono omax-≤L omax-≤L)
      lt12 =
        ≤o-sucMono (c1 ⊓Size c2 By hide)
        ≤⨟ omax-sucMono
          (omax-mono
            (omax∞-self (codeSize c1) ≤⨟ omax-≤L)
            (omax∞-self (codeSize c2) ≤⨟ omax-≤L))
      x1-12 = fromL ([ Approx ]⟨ c12 ⇐ c1 ⟩ x1 By
        hide {arg = lt1 })

      x2-12 = fromL ([ Approx ]⟨ c12 ⇐ c2 ⟩ x2 By hide {arg = lt2})
      y1-12 = fromL ([ Approx ]⟨ c12 ⇐ c1 ⟩ y1 By hide {arg = lt1 })
      y2-12 = fromL ([ Approx ]⟨ c12 ⇐ c2 ⟩ y2 By hide {arg = lt2})
      x12 = fromL ([ Approx ] c12 ∋ x1-12 ⊓ x2-12 By hide {arg = lt12 })
      y12 = fromL ([ Approx ] c12 ∋ y1-12 ⊓ y2-12 By hide {arg = lt12})

    in C≡ c12 x12 y12
codeMeet (Cμ tyCtor c1 D1 ixs1) (Cμ tyCtor c2 D2 ixs2)  (HEq {h1 = HCtor x₂} reflp) reflp reflp reflp reflp =
  Cμ tyCtor
    c12
    (λ d → descMeet {I1 = c1} {I2 = c2} {cB = C𝟙} (D1 d) (D2 d) lt12)
    ixs12
  where
    lt12 = omax-sucMono (omax-mono (omax∞-self _ ≤⨟ omax-≤L) (omax∞-self _ ≤⨟ omax-≤L))
    ltix12 = ≤o-sucMono ((c1 ⊓Size c2 By hide {arg = lt12})) ≤⨟ omax-sucMono (omax-mono (omax∞-self _ ≤⨟ omax-≤L) (omax∞-self _ ≤⨟ omax-≤L))
    --≤o-sucMono (c1 ⊓Size c2 By hide {arg = lt12}) ≤⨟ omax-sucMono (omax-mono omax-≤L omax-≤L)
    c12 = (c1 ⊓ c2 By hide {arg = lt12})
    lt112 = omax-sucMono
      (omax-monoR (c1 ⊓Size c2 By hide {arg = lt12})
      ≤⨟ omax-assocL (codeSize c1) (codeSize c1) (codeSize c2)
      ≤⨟ omax-mono (omax∞-idem∞ _) (omax∞-self _)
      ≤⨟ omax-mono omax-≤L omax-≤L)
    lt212 = omax-sucMono
      (omax-monoR ((c1 ⊓Size c2 By hide {arg = lt12}) ≤⨟ omax-commut (codeSize c1) (codeSize c2))
      ≤⨟ omax-assocL (codeSize c2) (codeSize c2) (codeSize c1)
      ≤⨟ omax-commut _ _
      ≤⨟ omax-mono (omax∞-self _ ≤⨟ omax-≤L) (omax∞-idem∞ _ ≤⨟ omax-≤L)
      )
    ixs1-12 = fromL ([ Approx  ]⟨ c12 ⇐ c1 ⟩ ixs1 By hide {arg = lt112})
    ixs2-12 = fromL ([ Approx ]⟨ c12 ⇐ c2 ⟩ ixs2 By hide {arg = lt212})
    ixs12 = fromL ([ Approx ] c12 ∋ ixs1-12 ⊓ ixs2-12 By hide {arg = ltix12})
    descMeet : ∀ {I1 I2 cB skel}
      → ℂDesc I1 cB skel
      → ℂDesc I2 cB skel
      → (ltI : omax ((codeSize I1) ) (codeSize I2) <o cSize)
      → ℂDesc (I1 ⊓ I2 By hide {arg = ltI}) cB skel
    descMeet (CodeModule.CEnd i) (CodeModule.CEnd i₁) lt = CEnd {!!}
    descMeet (CodeModule.CArg c D1) (CodeModule.CArg c₁ D2) lt = {!!}
    descMeet (CodeModule.CRec j D1) (CodeModule.CRec j₁ D2) lt = {!!}
    descMeet (CodeModule.CHRec c j D1) (CodeModule.CHRec c₁ j₁ D2) lt = {!!}
codeMeet (CodeModule.CCumul ⦃ suc< ⦄ c1) (CodeModule.CCumul {{inst}} c2) (HEq {h1 = .HCumul} reflp) reflp reflp reflp reflp = CCumul {{inst = inst}} (oCodeMeet (ℓself {{inst = inst}}) c1 c2 reflp reflp)
codeMeet CodeModule.C⁇ (CodeModule.CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet CodeModule.C℧ (CodeModule.CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet CodeModule.C𝟘 (CodeModule.CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet CodeModule.C𝟙 (CodeModule.CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet CodeModule.CType (CodeModule.CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet (CodeModule.CΠ c1 cod) (CodeModule.CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet (CodeModule.CΣ c1 cod) (CodeModule.CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet (CodeModule.C≡ c1 x y) (CodeModule.CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet (CodeModule.Cμ tyCtor c1 D x) (CodeModule.CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp



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
