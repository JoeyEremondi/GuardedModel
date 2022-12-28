
-- Bound on the size of the meet on codes, assuming we have meet, cast, etc. for smaller types


open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Equality
open import Constructors
open import UnkGerm
open import GuardedAlgebra
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude

open import ApproxExact
open import InductiveCodes
-- open import CodePair
open import Sizes

open import CastComp.Interface

module CastComp.CodeMeetSize {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ}  (csize vsize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed csize vsize)

  where

open import Code
open import Head
open import Util


open import CastComp.DescMeet{{dt = dt}} {{dg}} {{ic}}  (⁇Allowed) {ℓ} csize vsize scm
open import CastComp.CodeMeet {ℓ} (⁇Allowed) csize vsize scm
open SmallerCastMeet scm

open import Assumption


descMeetSize : ∀ {cB1 cB2 cBTarget skel oTop}
      → (D1 : ℂDesc cB1 skel)
      → (D2 : ℂDesc cB2 skel)
      → (lto : oTop <ₛ csize )
      → (ltB : (codeSize cBTarget ≤ₛ smax  (codeSize cB1)  (codeSize cB2)))
      → (lt : smax ( (descSize D1) ) ( (descSize D2)) ≤ₛ oTop)
      → descSize {cB = cBTarget} (descMeet D1 D2 lto ltB lt) ≤ₛ smax (descSize D1) (descSize D2)
descMeetSize (CodeModule.CEnd) (CodeModule.CEnd ) lto ltB lt = smax-≤L
descMeetSize (CodeModule.CArg c ar1 D1 cB' reflp) (CodeModule.CArg c₁ ar2 D2 cB'' reflp) lto ltB lt
  = ≤ₛ-sucMono
    (smax*-mono
      (≤ₛ-limiting (λ k → _ ⊓Size _ By _  ≤⨟ smax-mono (≤ₛ-cocone _) (≤ₛ-cocone _) )
      , descMeetSize D1 D2 lto (DescMeetArg.ltcB c ar1 D1 c₁ ar2 D2 lto ltB lt) (smax-mono (≤suc (smax*-≤-n (FLit 1))) (≤suc (smax*-≤-n (FLit 1)))
                                                                                  ≤⨟ lt)
      , smax-sucMono (smax-mono ltB (≤ₛ-limiting (λ k → _ ⊓Size _ By hide ≤⨟ smax-mono (≤ₛ-cocone _) (≤ₛ-cocone _))) ≤⨟ smax-swap4) , tt)
    ≤⨟ smax*-swap)
    ≤⨟ smax-sucMono ≤ₛ-refl
descMeetSize (CodeModule.CRec c j D1 cB' reflp) (CodeModule.CRec c₁ j₁ D2 cB'' reflp) lto ltB lt
  = ≤ₛ-sucMono
    (smax*-mono (
      ≤ₛ-limiting (λ k → _ ⊓Size _ By hide ≤⨟  smax-mono (≤ₛ-cocone _) (≤ₛ-cocone _))
      , descMeetSize D1 D2 lto ltB (DescMeetHRec.ltcB c j D1 c₁ j₁ D2 lto ltB lt)
      , smax-sucMono (smax-mono ltB (≤ₛ-limiting (λ k → _ ⊓Size _ By hide ≤⨟ smax-mono (≤ₛ-cocone _) (≤ₛ-cocone _))) ≤⨟ smax-swap4) , tt)
      ≤⨟ smax*-swap)
    ≤⨟ smax-sucMono ≤ₛ-refl


codeMeetSize : ∀ {h1 h2}
  → (c1 c2 : ℂ ℓ )
  → (view : HeadMatchView h1 h2)
  → (eq1 : h1 ≡p codeHead c1)
  → (eq2 : h2 ≡p codeHead c2)
  → (eq3 : smax (codeSize c1) ( codeSize c2) ≡p csize)
  → codeSize (codeMeet c1 c2 view eq1 eq2 eq3) ≤ₛ smax (codeSize c1) (codeSize c2)

codeMeetSize c1 c2 (H℧L reflp) eq1 eq2 reflp = codeMaxSuc {c1 = c1} {c2 = c2}
codeMeetSize c1 c2 (H℧R reflp) eq1 eq2 reflp = codeMaxSuc {c1 = c1} {c2 = c2}
codeMeetSize c1 c2 (HNeq x) eq1 eq2 reflp = codeMaxSuc {c1 = c1} {c2 = c2}
codeMeetSize c1 c2 (H⁇L reflp x₁) eq1 eq2 reflp = smax-≤R
codeMeetSize c1 c2 (H⁇R reflp) eq1 eq2 reflp = smax-≤L
codeMeetSize CodeModule.C𝟙 CodeModule.C𝟙 (HEq {h1 = H𝟙} reflp) eq1 eq2 reflp = smax-≤L
codeMeetSize CodeModule.C𝟘 CodeModule.C𝟘 (HEq {h1 = H𝟘} reflp) eq1 eq2 reflp = smax-≤L
codeMeetSize CodeModule.Cℕ CodeModule.Cℕ (HEq {h1 = Hℕ} reflp) eq1 eq2 reflp = smax-≤L
codeMeetSize CodeModule.CType CodeModule.CType (HEq {h1 = HType} reflp) reflp reflp reflp = smax-≤L
codeMeetSize (CodeModule.CΠ c1 cod) (CodeModule.CΠ c2 cod₁) (HEq {h1 = HΠ} reflp) eq1 eq2 reflp
  = ≤ₛ-sucMono
    (smax-mono
      ( (c1 ⊓Size c2 By hide) )
      ((≤ₛ-limiting  λ k → _ ⊓Size _ By hide ≤⨟ ≤ₛ-cocone  _ ≤⨟ ≤ₛ-cocone  _)
                 ≤⨟ smax-lim2L _ _)
      ≤⨟ smax-swap4)
  ≤⨟ smax-sucMono (≤ₛ-refl)
codeMeetSize (CodeModule.CΣ c1 cod) (CodeModule.CΣ c2 cod₁) (HEq {h1 = HΣ} reflp) eq1 eq2 reflp
  = ≤ₛ-sucMono
    (smax-mono
      ( (c1 ⊓Size c2 By hide) )
      ((≤ₛ-limiting  λ k → _ ⊓Size _ By hide ≤⨟ ≤ₛ-cocone  _ ≤⨟ ≤ₛ-cocone  _)
                 ≤⨟ smax-lim2L _ _)
      ≤⨟ smax-swap4)
  ≤⨟ smax-sucMono (≤ₛ-refl)
codeMeetSize (CodeModule.C≡ c1 x y) (CodeModule.C≡ c2 x₁ y₁) (HEq {h1 = H≅} reflp) eq1 eq2 reflp
  = ≤ₛ-sucMono ( (c1 ⊓Size c2 By hide) ) ≤⨟ smax-sucMono (≤ₛ-refl )
codeMeetSize (CodeModule.Cμ tyCtor c1 D x) (CodeModule.Cμ tyCtor₁ c2 D₁ x₁) (HEq {h1 = HCtor x₂} reflp) reflp reflp reflp
  = ≤ₛ-sucMono (smax-mono (_ ⊓Size _ By hide) (extFinLim _ _ (λ d → descMeetSize (D d) (D₁ d) (smax-sucMono (smax-mono (FinLim-cocone _ _ ≤⨟ smax-≤R) (FinLim-cocone _ _ ≤⨟ smax-≤R))) smax-≤L ≤ₛ-refl
    ≤⨟ FinLim-cocone _ d) ≤⨟ smax-FinLim2 _ _) ≤⨟ smax-swap4) ≤⨟ smax-sucMono ≤ₛ-refl
  -- ≤ₛ-sucMono (smax-mono ( (_ ⊓Size _ By hide) ) ( (extFinLim _ _ (λ d →  {!!}) ≤⨟ smax-FinLim2 _ _ ) ) ≤⨟ smax-swap4)
  -- ≤⨟ smax-sucMono (≤ₛ-refl )
codeMeetSize (CCumul ⦃ suc< ⦄ c1) (CCumul {{suc<}} c2) (HEq {h1 = .HCumul} reflp) reflp reflp reflp
  = oCodeMeetSize (self-1 true) c1 c2 reflp reflp
  -- ≤ₛ-sucMono (oCodeMeetSize self-1 reflp c1 c2 reflp)
  -- ≤⨟ smax-sucMono (≤ₛ-refl)
codeMeetSize C⁇ (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeetSize C℧ (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeetSize C𝟘 (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeetSize C𝟙 (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeetSize Cℕ (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeetSize CType (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeetSize (CΠ c1 cod) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeetSize (CΣ c1 cod) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeetSize (C≡ c1 x y) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeetSize (Cμ tyCtor c1 D x) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
-- codeMeetSize _ _ _ _ _ _ = {!!}
