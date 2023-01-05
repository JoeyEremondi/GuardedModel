
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


open import CastComp.DescMeet (⁇Allowed) {ℓ} csize vsize scm
open import CastComp.DescMeet (⁇Allowed) {ℓ} csize vsize scm
open import CastComp.CodeMeet {ℓ} (⁇Allowed) csize vsize scm
open SmallerCastMeet scm


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
codeMeetSize C𝟙 C𝟙 (HEq {h1 = H𝟙} reflp) eq1 eq2 reflp = smax-≤L
codeMeetSize C𝟘 C𝟘 (HEq {h1 = H𝟘} reflp) eq1 eq2 reflp = smax-≤L
codeMeetSize Cℕ Cℕ (HEq {h1 = Hℕ} reflp) eq1 eq2 reflp = smax-≤L
codeMeetSize (CType {{inst}}) CType  (HEq {h1 = HType} reflp) eq1 eq2 reflp = smax-≤L
codeMeetSize (CΠ c1 cod) (CΠ c2 cod₁) (HEq {h1 = HΠ} reflp) eq1 eq2 reflp
  =
    ≤ₛ-sucMono
    (smax-mono
      ( (c1 ⊓Size c2 By hide) )
      ((≤ₛ-limiting  λ k → _ ⊓Size _ By hide ≤⨟ ≤ₛ-cocone  _ ≤⨟ ≤ₛ-cocone  _)
                 ≤⨟ smax-lim2L _ _)
      ≤⨟ smax-swap4)
  ≤⨟ smax-sucMono (≤ₛ-refl)
codeMeetSize (CΣ c1 cod) (CΣ c2 cod₁) (HEq {h1 = HΣ} reflp) eq1 eq2 reflp
  = ≤ₛ-sucMono
    (smax-mono
      ( (c1 ⊓Size c2 By hide) )
      ((≤ₛ-limiting  λ k → _ ⊓Size _ By hide ≤⨟ ≤ₛ-cocone  _ ≤⨟ ≤ₛ-cocone  _)
                 ≤⨟ smax-lim2L _ _)
      ≤⨟ smax-swap4)
  ≤⨟ smax-sucMono (≤ₛ-refl)
codeMeetSize (C≡ c1 x y) (C≡ c2 x₁ y₁) (HEq {h1 = H≅} reflp) eq1 eq2 reflp
  = ≤ₛ-sucMono ( (c1 ⊓Size c2 By hide) ) ≤⨟ smax-sucMono (≤ₛ-refl )
codeMeetSize (Cμ tyCtor c1 D1 ixs1) (Cμ tyCtor c2 D2 ixs2)  (HEq {h1 = HCtor x₂} reflp) reflp reflp reflp
  = ≤ₛ-sucMono (smax-mono (_ ⊓Size _ By hide) (extFinLim _ _ (λ d → descMeetSize (D1 d) (D2 d) (smax-sucMono (smax-mono (FinLim-cocone _ _ ≤⨟ smax-≤R) (FinLim-cocone _ _ ≤⨟ smax-≤R))) smax-≤L ≤ₛ-refl
    ≤⨟ FinLim-cocone _ d) ≤⨟ smax-FinLim2 _ _) ≤⨟ smax-swap4) ≤⨟ smax-sucMono ≤ₛ-refl
  -- ≤ₛ-sucMono (smax-mono ( (_ ⊓Size _ By hide) ) ( (extFinLim _ _ (λ d →  {!!}) ≤⨟ smax-FinLim2 _ _ ) ) ≤⨟ smax-swap4)
  -- ≤⨟ smax-sucMono (≤ₛ-refl )
codeMeetSize (CCumul ⦃ suc< ⦄ c1) (CCumul {{inst}} c2) (HEq {h1 = .HCumul} reflp) reflp reflp reflp
  = oCodeMeetSize (self-1 true) c1 c2 reflp reflp
  -- ≤ₛ-sucMono (oCodeMeetSize self-1 reflp c1 c2 reflp)
  -- ≤⨟ smax-sucMono (≤ₛ-refl)
-- codeMeetSize C⁇ (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
-- codeMeetSize C℧ (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeetSize c0 c1 h pf eq1 eq2 = {!c0 c1 h!}
-- codeMeetSize C𝟘 (CCumul ⦃ suc< ⦄ c2f) (HEq {h1 = .HCumul} reflp) () reflp reflp
-- codeMeetSize C𝟙 (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
-- codeMeetSize Cℕ (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
-- codeMeetSize CType (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
-- codeMeetSize (CΠ c1 cod) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
-- codeMeetSize (CΣ c1 cod) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
-- codeMeetSize (C≡ c1 x y) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
-- codeMeetSize (Cμ tyCtor c1 D x) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp

codeMeetSize c0 c1 h pf eq1 eq2 = {!c0 c1 h!}
