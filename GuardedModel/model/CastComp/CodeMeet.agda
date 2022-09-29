-- Implementation of the meet on codes, assuming we have meet, cast, etc. for smaller types


open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (≤-refl to ≤ℕ-refl)
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
open import WellFounded

open import CastComp.Interface

module CastComp.CodeMeet {{dt : DataTypes}} {{dg : DataGerms}} {{ic : InductiveCodes}} {{dgs : DataGermsSmaller}}
    (⁇Allowed : Bool){ℓ} (cSize : Size) (vSize : Size) (scm : SmallerCastMeet ⁇Allowed ℓ cSize vSize)

  where

open import Code
open import Head
open import Util


open SmallerCastMeet scm
open import CastComp.DescMeet {{dt}} {{dg}} {{ic}} {{dgs}} ⁇Allowed {ℓ} cSize vSize scm

{-# DISPLAY SmallerCastMeet._⊓_By_  = _⊓_By_  #-}
{-# DISPLAY SmallerCastMeet._∋_⊓_By_  = _∋_⊓_By_  #-}

codeMeet : ∀ {{_ : Æ}} {h1 h2}
  → (c1 c2 : ℂ ℓ )
  → (view : HeadMatchView h1 h2)
  → (eq1 : h1 ≡p codeHead c1)
  → (eq2 : h2 ≡p codeHead c2)
  → (smax (codeSize c1) ( codeSize c2) ≡p cSize)
  → (SZ ≡p vSize)
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
          dom12 = dom1 ⊓ dom2
            By hide {arg = smax-strictMono (≤ₛ-sucMono smax-≤L) (≤ₛ-sucMono smax-≤L)}
          cod12 : (x : ApproxEl dom12) → ℂ ℓ
          cod12 x12 =
            let (x1 , x2) = fromL ([ Approx ]⟨ dom1 , dom2 ⇐⊓⟩ x12 By hide {arg = smax-sucMono (smax-mono smax-≤L smax-≤L)} )
            in  (cod1 x1 ) ⊓ cod2 x2
                      By hide {arg =
                        smax-strictMono
                          (≤ₛ-sucMono (≤ₛ-cocone {{æ = Approx}} _ ≤⨟ smax-≤R))
                          (≤ₛ-sucMono (≤ₛ-cocone {{æ = Approx}} _ ≤⨟ smax-≤R)) }
        in CΠ dom12 cod12
codeMeet (CΣ dom1 cod1) (CΣ dom2 cod2)  (HEq {h1 = HΣ} reflp) eq1 eq2 reflp reflp
        = let
          dom12 = dom1 ⊓ dom2
            By hide {arg = smax-strictMono (≤ₛ-sucMono smax-≤L) (≤ₛ-sucMono smax-≤L)}
          cod12 : (x : ApproxEl dom12) → ℂ ℓ
          cod12 x12 =
            let (x1 , x2) = fromL ([ Approx ]⟨ dom1 , dom2 ⇐⊓⟩ x12 By hide {arg = smax-sucMono (smax-mono smax-≤L smax-≤L)} )
            in  (cod1 x1 ) ⊓ cod2 x2
                      By hide {arg =
                        smax-strictMono
                          (≤ₛ-sucMono (≤ₛ-cocone {{æ = Approx}} _ ≤⨟ smax-≤R))
                          (≤ₛ-sucMono (≤ₛ-cocone {{æ = Approx}} _ ≤⨟ smax-≤R)) }
        in CΣ dom12 cod12
codeMeet (C≡ c1 x1 y1) (C≡ c2 x2 y2)  (HEq {h1 = H≅} reflp) eq1 eq2 reflp reflp
  = let
      c12 = c1 ⊓ c2
        By hide {arg = smax-strictMono ≤ₛ-refl ≤ₛ-refl}
      x12 = fromL ([ Approx ] c1 ,, c2 ∋ x1 ⊓ x2 By hide {arg = smax-strictMono ≤ₛ-refl ≤ₛ-refl})

      y12 = fromL ([ Approx ] c1 ,, c2 ∋ y1 ⊓ y2 By hide {arg = smax-strictMono ≤ₛ-refl ≤ₛ-refl})

    in C≡ c12 x12 y12 --x12 y12
codeMeet (Cμ tyCtor c1 D1 ixs1) (Cμ tyCtor c2 D2 ixs2)  (HEq {h1 = HCtor x₂} reflp) reflp reflp reflp reflp =
  Cμ tyCtor
    (c1 ⊓ c2
      By hide  )
    (λ d → descMeet
      (D1 d)
      (D2 d)
      (smax-strictMono ≤ₛ-refl ≤ₛ-refl)
      (smax-mono smax-≤L smax-≤L)
      smax-≤L
      (smax-mono
        (DLim-cocone tyCtor _ d ≤⨟ smax-≤R)
        (DLim-cocone tyCtor _ d ≤⨟ smax-≤R)
      )
    )
    (fromL ([ Approx ] c1 ,, c2 ∋ ixs1 ⊓ ixs2 By hide {arg = smax-strictMono (≤ₛ-sucMono smax-≤L) (≤ₛ-sucMono smax-≤L)}))

codeMeet (CCumul ⦃ suc< ⦄ c1) (CCumul {{inst}} c2) (HEq {h1 = .HCumul} reflp) reflp reflp reflp reflp = CCumul {{inst = inst}} (oCodeMeet (self-1 {{inst = inst}}) c1 c2 reflp reflp)
codeMeet C⁇ (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet C℧ (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet C𝟘 (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet C𝟙 (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet CType (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet (CΠ c1 cod) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet (CΣ c1 cod) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet (C≡ c1 x y) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp
codeMeet (Cμ tyCtor c1 D x) (CCumul ⦃ suc< ⦄ c2) (HEq {h1 = .HCumul} reflp) () reflp reflp reflp



-- --     -- Otherwise, we have two codes with the same head
-- --     -- Trivial cases with no arguments: both inputs are identical
-- --     codeMeet (C𝟙 |wf| wf1) (C𝟙 |wf| wf2) reflp reflp | HStatic H𝟙  | .(HStatic H𝟙)  | HEq reflp = C𝟙 |wf| IWF𝟙
-- --     codeMeet (C𝟘 |wf| wf1) (C𝟘 |wf| wf2) reflp reflp | HStatic H𝟘  | .(HStatic H𝟘)  | HEq reflp = C𝟘 |wf| IWF𝟘
-- --     codeMeet (CType {{suc<}} |wf| wf1) (CType |wf| wf2) reflp reflp | HStatic HType  | .(HStatic HType)  | HEq reflp = CType {{_}} {{_}} {{suc<}} |wf| IWFType
-- --     codeMeet (CΠ dom1 cod1 |wf| (IWFΠ domwf1 codwf1)) (CΠ dom2 cod2 |wf| (IWFΠ domwf2 codwf2)) reflp reflp | HStatic HΠ  | .(HStatic HΠ)  | HEq reflp
-- --       =
-- --         let
-- --           dom12 = (dom1 |wf| domwf1) ⊓ (dom2 |wf| domwf2)
-- --                         By ≤o-sucMono smax-≤L
-- --           cod12 : (x : wfApproxEl dom12) → ℂwf ℓ
-- --           cod12 x12 =
-- --             let
-- --               x1 = [ Approx ]⟨ dom1 |wf| domwf1 ⇐ dom12 ⟩ x12 By ≤o-sucMono smax-≤L
-- --               x2 = [ Approx ]⟨ dom2 |wf| domwf2 ⇐ dom12 ⟩ x12 By {!!}
-- --             in
-- --               (cod1 (fromL x1) |wf| codwf1 _) ⊓ cod2 (fromL x2) |wf| codwf2 _
-- --                       By {!!}
-- --         in CΠ
-- --           (code dom12)
-- --           {!λ x → !}
-- --         |wf| {!!}
-- --     codeMeet (CΣ c1 cod |wf| wf1) (CΣ c2 cod₁ |wf| wf2) reflp reflp | HStatic HΣ  | .(HStatic HΣ)  | HEq reflp = {!!}
-- --     codeMeet (C≡ c1 x y |wf| wf1) (C≡ c2 x₁ y₁ |wf| wf2) reflp reflp | HStatic H≅  | .(HStatic H≅)  | HEq reflp = {!!}
-- --     codeMeet (Cμ tyCtor c1 D x |wf| wf1) (Cμ tyCtor₁ c2 D₁ x₁ |wf| wf2) reflp reflp | HStatic (HCtor x₂)  | .(HStatic (HCtor x₂))  | HEq reflp = {!!}
