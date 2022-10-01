
-- Bound on the size of the meet on codes, assuming we have meet, cast, etc. for smaller types


open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Vec
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
open import SizeOrd

open import CastComp.Interface

module CastComp.CodeMeetSize {{dt : DataTypes}} {{dg : DataGerms}} {{ic : InductiveCodes}} {{dgs : DataGermsSmaller}}
    (⁇Allowed : Bool) {ℓ} (cSize : Size) (vSize : Size) (scm : SmallerCastMeet ⁇Allowed ℓ cSize vSize)

  where

open import Code
open import Head
open import Util


open import CastComp.DescMeet{{dt = dt}} {{dg}} {{ic}} {{dgs}} (⁇Allowed) {ℓ} cSize vSize scm
open import CastComp.CodeMeet {{dt}} {{dg}} {{ic}} {{dgs}} (⁇Allowed) {ℓ} cSize vSize scm
open SmallerCastMeet scm


descMeetSize : ∀ {I1 I2 cB1 cB2 cBTarget skel oTop}
      → (D1 : ℂDesc I1 cB1 skel)
      → (D2 : ℂDesc I2 cB2 skel)
      → (lto : oTop <ₛ cSize )
      → (ltI : smax ((codeSize I1) ) ((codeSize I2)) ≤ₛ oTop)
      → (ltB : (codeSize cBTarget ≤ₛ smax  (codeSize cB1)  (codeSize cB2)))
      → (lt : smax ( (descSize D1) ) ( (descSize D2)) ≤ₛ oTop)
      → descSize {cB = cBTarget} (descMeet D1 D2 lto ltI ltB lt) ≤ₛ smax (descSize D1) (descSize D2)
descMeetSize (CodeModule.CEnd i) (CodeModule.CEnd i₁) lto ltI ltB lt = smax-≤L
descMeetSize (CodeModule.CArg c D1 cB' reflp) (CodeModule.CArg c₁ D2 cB'' reflp) lto ltI ltB lt
  = ≤ₛ-sucMono (smax*-mono (
    smax-sucMono (smax-mono ltB ((≤ₛ-limiting {{æ = Approx}}  λ k → _ ⊓Size _ By hide
      ≤⨟ ≤ₛ-cocone {{æ = Approx}} _
      ≤⨟ ≤ₛ-cocone {{æ = Approx}} _ )
      ≤⨟ smax-lim2L _ _) ≤⨟ smax-swap4)
    , (≤ₛ-limiting {{æ = Approx}}  λ k → _ ⊓Size _ By hide
                   ≤⨟ ≤ₛ-cocone {{æ = Approx}} _
                   ≤⨟ ≤ₛ-cocone {{æ = Approx}} _)
      ≤⨟ smax-lim2L _ _
    , descMeetSize D1 D2 lto ltI _ _ , tt)
  ≤⨟ smax*-swap)
    ≤⨟ smax-sucMono ≤ₛ-refl
  -- ≤⨟ smax-sucMono ≤ₛ-refl
  -- = ≤ₛ-sucMono (smax*-mono (
  --              ≤ₛ-sucMono (smax-monoR
  --                         ?
  --                         -- ( (≤ₛ-limiting {{æ = Approx}} _ λ k → ≤ₛ-cocone ⦃ æ = Approx ⦄ _ _ (≤ₛ-cocone ⦃ æ = Approx ⦄ _ _ ( (_ ⊓Size _ By hide) )) ≤⨟ smax-lim2L _ _ ) )
  --              ≤⨟ smax-swap4)
  --              , ? -- (≤ₛ-limiting {{æ = Approx}} _ λ k → ≤ₛ-cocone ⦃ æ = Approx ⦄ _ _ (≤ₛ-cocone ⦃ æ = Approx ⦄ _ _ ( (_ ⊓Size _ By hide) )))
  --                ≤⨟ smax-lim2L _ _
  --              , descMeetSize D1 D2 _ _ _ _ , tt)
  --   ≤⨟ smax*-swap)
  --   ≤⨟ smax-sucMono (≤ₛ-refl _)
descMeetSize (CodeModule.CRec j D1) (CodeModule.CRec j₁ D2) lto ltI ltB lt
  = ≤ₛ-sucMono (descMeetSize D1 D2 lto ltI ltB (smax-mono (≤↑ _) (≤↑ _) ≤⨟ lt ))
  ≤⨟ smax-sucMono ≤ₛ-refl
-- ≤ₛ-sucMono (descMeetSize D1 D2 lto ltI ltB (smax-mono (≤↑ (descSize D1)) (≤↑ (descSize D2)) ≤⨟ lt)) ≤⨟ smax-sucMono (≤ₛ-refl _)
descMeetSize (CodeModule.CHRec c j D1 cB' reflp) (CodeModule.CHRec c₁ j₁ D2 cB'' reflp) lto ltI ltB lt
  = ≤ₛ-sucMono (smax*-mono (
               ≤ₛ-sucMono (smax-mono
                 ltB
                 ((≤ₛ-limiting {{æ = Approx}} λ k → _ ⊓Size _ By hide ≤⨟ ≤ₛ-cocone {{æ = Approx}} _ ≤⨟ ≤ₛ-cocone {{æ = Approx}} _)
                 ≤⨟ smax-lim2L _ _)
               ≤⨟ smax-swap4) ≤⨟ smax-sucMono ≤ₛ-refl
               , (≤ₛ-limiting {{æ = Approx}} λ k → _ ⊓Size _ By hide ≤⨟ ≤ₛ-cocone {{æ = Approx}} _ ≤⨟ ≤ₛ-cocone {{æ = Approx}} _)
                 ≤⨟ smax-lim2L _ _
               , descMeetSize D1 D2 _ _ _ _ , tt)
               ≤⨟ smax*-swap)
    ≤⨟ smax-sucMono ≤ₛ-refl
   -- = ≤ₛ-sucMono (smax*-mono (
   --   ≤ₛ-sucMono (smax-monoR
   --              ?
   --              -- ( ((≤ₛ-limiting {{æ = Approx}} _ λ k → ≤ₛ-cocone ⦃ æ = Approx ⦄ _ _ (≤ₛ-cocone ⦃ æ = Approx ⦄ _ _ (smax∞-mono (_ ⊓Size _ By hide) ≤⨟ smax∞-distR) )) ≤⨟ smax-lim2L _ _) ≤⨟ smax∞-distR)

   --              ≤⨟ smax-swap4) ≤⨟ smax-sucMono (≤ₛ-refl _)
   --   , (≤ₛ-limiting {{æ = Approx}} _ λ k → ≤ₛ-cocone ⦃ æ = Approx ⦄ _ _ (≤ₛ-cocone ⦃ æ = Approx ⦄ _ _ ( (_ ⊓Size _ By hide) ) )) ≤⨟ smax-lim2L _ _
   --   , descMeetSize D1 D2 _ _ _ _ , tt) ≤⨟ smax*-swap)
   -- ≤⨟ smax-sucMono (≤ₛ-refl _)


-- codeMeetSize : ∀ {{_ : Æ}} {h1 h2}
--   → (c1 c2 : ℂ ℓ )
--   → (view : HeadMatchView h1 h2)
--   → (eq1 : h1 ≡p codeHead c1)
--   → (eq2 : h2 ≡p codeHead c2)
--   → (eq3 : smax (codeSize c1) ( codeSize c2) ≡p cSize)
--   → (eq4 : OZ ≡p vSize)
--   → codeSize (codeMeet c1 c2 view eq1 eq2 eq3 eq4) ≤ₛ smax (codeSize c1) (codeSize c2)

-- codeMeetSize c1 c2 (H℧L reflp) eq1 eq2 reflp reflp = codeMaxSuc
-- codeMeetSize c1 c2 (H℧R reflp) eq1 eq2 reflp reflp = codeMaxSuc
-- codeMeetSize c1 c2 (H⁇L reflp x₁) eq1 eq2 reflp reflp = smax-≤R
-- codeMeetSize c1 c2 (H⁇R reflp) eq1 eq2 reflp reflp = smax-≤L
-- codeMeetSize c1 c2 (HNeq x) eq1 eq2 reflp reflp = codeMaxSuc
-- codeMeetSize (CodeModule.CΠ c1 cod) (CodeModule.CΠ c2 cod₁) (HEq {h1 = HΠ} reflp) eq1 eq2 reflp reflp
--   = ≤ₛ-sucMono
--     (smax-mono
--       (smax∞-mono (c1 ⊓Size c2 By hide) ≤⨟ smax∞-distR)
--       (smax∞-mono (≤ₛ-limiting {{æ = Approx}} _ λ k → ≤ₛ-cocone {{æ = Approx}} _ _ (≤ₛ-cocone ⦃ æ = Approx ⦄ _ _ (smax∞-mono (_ ⊓Size _ By hide) ≤⨟ smax∞-distR)) ≤⨟ smax-lim2L _ _ )  ≤⨟ smax∞-distR )
--       -- (≤ₛ-limiting ⦃ æ = Approx ⦄ _ (λ k →
--       --   ≤ₛ-cocone ⦃ æ = Approx ⦄ _ _ (≤ₛ-cocone ⦃ æ = Approx ⦄ _ _ (smax∞-mono (_ ⊓Size _ By hide) ≤⨟ smax∞-distR))
--       --   ≤⨟ smax-lim2L (λ x → (codeSize (cod x))) (λ x → (codeSize (cod₁ x)))))
--       ≤⨟ smax-swap4)
--   ≤⨟ smax-sucMono (≤ₛ-refl _)
-- codeMeetSize (CodeModule.CΣ c1 cod) (CodeModule.CΣ c2 cod₁) (HEq {h1 = HΣ} reflp) eq1 eq2 reflp reflp
--   = ≤ₛ-sucMono
--     (smax-mono
--       (smax∞-mono (c1 ⊓Size c2 By hide) ≤⨟ smax∞-distR)
--       (smax∞-mono (≤ₛ-limiting {{æ = Approx}} _ λ k → ≤ₛ-cocone {{æ = Approx}} _ _ (≤ₛ-cocone ⦃ æ = Approx ⦄ _ _ (smax∞-mono (_ ⊓Size _ By hide) ≤⨟ smax∞-distR)) ≤⨟ smax-lim2L _ _ )  ≤⨟ smax∞-distR )
--       -- (≤ₛ-limiting ⦃ æ = Approx ⦄ _ (λ k →
--       --   ≤ₛ-cocone ⦃ æ = Approx ⦄ _ _ (≤ₛ-cocone ⦃ æ = Approx ⦄ _ _ (smax∞-mono (_ ⊓Size _ By hide) ≤⨟ smax∞-distR))
--       --   ≤⨟ smax-lim2L (λ x → (codeSize (cod x))) (λ x → (codeSize (cod₁ x)))))
--       ≤⨟ smax-swap4)
--   ≤⨟ smax-sucMono (≤ₛ-refl _)
-- codeMeetSize (CodeModule.C≡ c1 x y) (CodeModule.C≡ c2 x₁ y₁) (HEq {h1 = H≅} reflp) eq1 eq2 reflp reflp
--   = ≤ₛ-sucMono (smax∞-mono (c1 ⊓Size c2 By hide) ≤⨟ smax∞-distR) ≤⨟ smax-sucMono (≤ₛ-refl _)
-- codeMeetSize CodeModule.C𝟙 CodeModule.C𝟙 (HEq {h1 = H𝟙} reflp) eq1 eq2 reflp reflp = smax-≤L
-- codeMeetSize CodeModule.C𝟘 CodeModule.C𝟘 (HEq {h1 = H𝟘} reflp) eq1 eq2 reflp reflp = smax-≤L
-- codeMeetSize CodeModule.CType CodeModule.CType (HEq {h1 = HType} reflp) reflp reflp reflp reflp = smax-≤L
-- codeMeetSize (CodeModule.Cμ tyCtor c1 D x) (CodeModule.Cμ tyCtor₁ c2 D₁ x₁) (HEq {h1 = HCtor x₂} reflp) reflp reflp reflp reflp
--   = ≤ₛ-sucMono (smax-mono (smax∞-mono (_ ⊓Size _ By hide) ≤⨟ smax∞-distR) (smax∞-mono (extDLim tyCtor _ _ (λ d → descMeetSize (D d) (D₁ d) _ _ _ _ ≤⨟ DLim-cocone tyCtor _ d) ≤⨟ smax-DLim2 _ _ _ ) ≤⨟ smax∞-distR) ≤⨟ smax-swap4)
--   ≤⨟ smax-sucMono (≤ₛ-refl _)
-- codeMeetSize (CCumul ⦃ suc< ⦄ c1) (CCumul {{inst}} c2) (HEq {h1 = .HCumul} reflp) reflp reflp reflp reflp = ≤ₛ-sucMono (oCodeMeetSize (ℓself {{inst = inst}}) c1 c2 reflp reflp) ≤⨟ smax-sucMono (≤ₛ-refl _)
-- codeMeetSize C⁇ (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
-- codeMeetSize C℧ (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
-- codeMeetSize C𝟘 (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
-- codeMeetSize C𝟙 (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
-- codeMeetSize CType (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
-- codeMeetSize (CΠ c1 cod) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
-- codeMeetSize (CΣ c1 cod) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
-- codeMeetSize (C≡ c1 x y) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
-- codeMeetSize (Cμ tyCtor c1 D x) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
