-- Implementation of the meet on codes, assuming we have meet, cast, etc. for smaller types


open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (≤-refl to ≤ℕ-refl)
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Equality
open import UnkGerm
open import GuardedAlgebra
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude

open import ApproxExact
open import InductiveCodes
open import Sizes
open import Constructors
-- open import CodePair
--


open import CastComp.Interface

module CastComp.CodeMeet {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
     {ℓ} (⁇Allowed : Bool) (csize vsize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed csize vsize)

  where


open import CastComp.DescMeet ⁇Allowed csize vsize scm
open import CastComp.DescMeetSize ⁇Allowed csize vsize scm

open import Code
open import Head
open import Util


open SmallerCastMeet scm
-- open import CastComp.DescMeet {{dt}} {{dg}} {{ic}} ⁇Allowed {ℓ} size scm

open import Assumption

{-# DISPLAY SmallerCastMeet._⊓_By_  = _⊓_By_  #-}
{-# DISPLAY SmallerCastMeet._∋_⊓_By_  = _∋_⊓_By_  #-}

codeMeet : ∀ {h1 h2}
  → (c1 c2 : ℂ ℓ )
  → (view : HeadMatchView h1 h2)
  → (eq1 : h1 ≡p codeHead c1)
  → (eq2 : h2 ≡p codeHead c2)
  → (smax (codeSize c1) ( codeSize c2) ≡p csize)
  → Σ[ cRet ∈ ℂ ℓ ]( codeSize cRet ≤ₛ csize )




-- Error cases: the meet is ℧ if either argument is ℧
-- or the heads don't match
codeMeet _ c2  (H℧L reflp) eq1 eq2 reflp =
  C℧
        ---------------------------
        , codeMaxSuc
codeMeet c1 _  (H℧R reflp) eq1 eq2 reflp =
  C℧
        -------------------------------
        , codeMaxSuc
codeMeet c1 c2  (HNeq x) eq1 eq2 reflp = C℧
        -------------------------------
        , codeMaxSuc
-- Meet of anything with ⁇ is that thing
codeMeet _ c2  (H⁇L reflp x₁) eq1 eq2 reflp =
  c2
        ------------------------------
        , smax-≤R
codeMeet c1 _  (H⁇R reflp) eq1 eq2 reflp =
  c1
        ----------------------------
        , smax-≤L
-- Otherwise, we have two codes with the same head, so we take the meet of the parts
-- after performing the required casts
-- First: trivial cases, where both types are identical
codeMeet C𝟙 C𝟙  (HEq {h1 = H𝟙} reflp) eq1 eq2 reflp =
  C𝟙
        --------------------------------
        , codeMaxSuc
codeMeet C𝟘 C𝟘  (HEq {h1 = H𝟘} reflp) eq1 eq2 reflp =
  C𝟘
        ---------------------------------
        , codeMaxSuc
codeMeet Cℕ Cℕ  (HEq {h1 = Hℕ} reflp) eq1 eq2 reflp =
  Cℕ
        -------------------------------------
        , codeMaxSuc
codeMeet (CType {{inst}}) CType  (HEq {h1 = HType} reflp) eq1 eq2 reflp =
  CType {{inst = inst}}
  -----------------------------------------
  , codeMaxSuc
-- Pi and Sigma types: we take the meet of the domains, then produce a codomain that takes the meet
-- after casting the argument to the appropriate type
codeMeet (CΠ dom1 cod1) (CΠ dom2 cod2)  (HEq {h1 = HΠ} reflp) eq1 eq2 reflp
        = let
          dom12 = dom1 ⊓ dom2
            By Decreasing
              smax-strictMono (≤ₛ-sucMono smax-≤L) (≤ₛ-sucMono smax-≤L)
          cod12 : (x : ApproxEl dom12) → ℂ ℓ
          cod12 x12 =
            let
              (x1 , x2) =
                ⟨ dom1 , dom2 ⇐⊓⟩ x12
                --------------------------------
                      approxBy Decreasing
                        smax-sucMono (smax-mono smax-≤L smax-≤L)
            in  cod1 x1 ⊓ cod2 x2
                      ---------------------------------------
                        By Decreasing
                          smax-strictMono
                            (≤ₛ-sucMono (≤ₛ-cocone _ ≤⨟ smax-≤R))
                            (≤ₛ-sucMono (≤ₛ-cocone _ ≤⨟ smax-≤R))
        in CΠ dom12 cod12
                  -------------------------------------------------------------------
                  ,  ≤ₛ-sucMono
                      (smax-mono
                        ( (dom1 ⊓Size dom2 By hide) )
                        ((≤ₛ-limiting  λ k → _ ⊓Size _ By hide ≤⨟ ≤ₛ-cocone  _ ≤⨟ ≤ₛ-cocone  _)
                                  ≤⨟ smax-lim2L _ _)
                        ≤⨟ smax-swap4)
                    ≤⨟ smax-sucMono (≤ₛ-refl)
codeMeet (CΣ dom1 cod1) (CΣ dom2 cod2)  (HEq {h1 = HΣ} reflp) eq1 eq2 reflp
        = let
          dom12 = dom1 ⊓ dom2
            By Decreasing smax-strictMono (≤ₛ-sucMono smax-≤L) (≤ₛ-sucMono smax-≤L)
          cod12 : (x : ApproxEl dom12) → ℂ ℓ
          cod12 x12 =
            let
              (x1 , x2) =
                ⟨ dom1 , dom2 ⇐⊓⟩ x12
                        ---------------------------------
                        approxBy Decreasing
                          smax-sucMono (smax-mono smax-≤L smax-≤L)
            in  (cod1 x1 ) ⊓ cod2 x2
                      -----------------------------------
                        By Decreasing
                          smax-strictMono
                            (≤ₛ-sucMono (≤ₛ-cocone _ ≤⨟ smax-≤R))
                            (≤ₛ-sucMono (≤ₛ-cocone _ ≤⨟ smax-≤R))
        in CΣ dom12 cod12
                  -------------------------------------------------------------------
                  ,  ≤ₛ-sucMono
                      (smax-mono
                        ( (dom1 ⊓Size dom2 By hide) )
                        ((≤ₛ-limiting  λ k → _ ⊓Size _ By hide ≤⨟ ≤ₛ-cocone  _ ≤⨟ ≤ₛ-cocone  _)
                                  ≤⨟ smax-lim2L _ _)
                        ≤⨟ smax-swap4)
                    ≤⨟ smax-sucMono (≤ₛ-refl)
codeMeet (C≡ c1 x1 y1) (C≡ c2 x2 y2)  (HEq {h1 = H≅} reflp) eq1 eq2 reflp
  = let
      c12 = c1 ⊓ c2
              ---------------------------------
              By Decreasing
                smax-strictMono ≤ₛ-refl ≤ₛ-refl
      x12 =
        [ c1 ⊓ c2 ]∋ x1 ⊓ x2
               ------------------------------------
                approxBy Decreasing
                  smax-strictMono ≤ₛ-refl ≤ₛ-refl

      y12 =  [ c1 ⊓ c2 ]∋ y1 ⊓ y2
                ------------------------------------------
                approxBy Decreasing
                  smax-strictMono ≤ₛ-refl ≤ₛ-refl

    in C≡ c12 x12 y12
                --------------------------------------------
                , ≤ₛ-sucMono ( (c1 ⊓Size c2 By hide) ) ≤⨟ smax-sucMono (≤ₛ-refl )
codeMeet (Cμ tyCtor c1 D1 ixs1) (Cμ tyCtor c2 D2 ixs2)  (HEq {h1 = HCtor x₂} reflp) reflp reflp reflp =
  let
    cIxRet =
      c1 ⊓ c2
            -------------------
            By Decreasing smax-sucMono (smax-mono smax-≤L smax-≤L)
    DRet =
      (λ d → descMeet (D1 d) (D2 d) (smax-sucMono (smax-mono (FinLim-cocone _ d ≤⨟ smax-≤R) (FinLim-cocone _ d ≤⨟ smax-≤R))) smax-≤L ≤ₛ-refl)
    ixRet =
      [ c1 ⊓ c2 ]∋ ixs1 ⊓ ixs2
          ------------------------------------------------------------
          approxBy Decreasing smax-sucMono (smax-mono smax-≤L smax-≤L)
    in Cμ tyCtor cIxRet DRet ixRet
          --------------------------------------------------------------------
          , ≤ₛ-sucMono (smax-mono (_ ⊓Size _ By hide) (extFinLim _ _ (λ d → descMeetSize (D1 d) (D2 d) (smax-sucMono (smax-mono (FinLim-cocone _ _ ≤⨟ smax-≤R) (FinLim-cocone _ _ ≤⨟ smax-≤R))) smax-≤L ≤ₛ-refl
          ≤⨟ FinLim-cocone _ d) ≤⨟ smax-FinLim2 _ _) ≤⨟ smax-swap4) ≤⨟ smax-sucMono ≤ₛ-refl

codeMeet (CCumul ⦃ suc< ⦄ c1) (CCumul {{inst}} c2) (HEq {h1 = .HCumul} reflp) reflp reflp reflp =
  CCumul {{inst = inst}} (oCodeMeet (self-1 true {{inst = inst}}) c1 c2 reflp reflp)
        --------------------------------------------------
        , oCodeMeetSize (self-1 true) c1 c2 reflp reflp


------------------------------------------------------------------------------
-- Impossible cases
codeMeet C⁇ (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeet C℧ (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeet C𝟘 (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeet C𝟙 (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeet Cℕ (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeet CType (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeet (CΠ c1 cod) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeet (CΣ c1 cod) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeet (C≡ c1 x y) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
codeMeet (Cμ tyCtor c1 D x) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp
