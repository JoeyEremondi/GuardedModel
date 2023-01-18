

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

module CastComp.CodeMeetArity {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ}  (csize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed csize)

  where

open import Code
open import Head
open import Util


open import CastComp.DescMeet {{dt = dt}} {{dg}} {{ic}}  (⁇Allowed) {ℓ} csize scm
open import CastComp.CodeMeet {ℓ} (⁇Allowed) csize scm
open SmallerCastMeet scm



codeMeetNested : ∀ {h1 h2 n}
  → (c1 c2 : ℂ ℓ )
  → (view : HeadMatchView h1 h2)
  → (eq1 : h1 ≡p codeHead c1)
  → (eq2 : h2 ≡p codeHead c2)
  → (eq3 : smax (codeSize c1) ( codeSize c2) ≡p csize)
  → IsNestedΣ n c1
  → IsNestedΣ n c2
  → IsNestedΣ n (fst (codeMeet c1 c2 view eq1 eq2 eq3))
codeMeetNested c1 c2 view eq1 eq2 eq3 Arity0 Arity0 = Arity0
codeMeetNested (CΣ dom1 cod1) (CΣ dom2 cod2) (HEq {h1 = HΣ} reflp) eq1 eq2 reflp (ArityΣ ar1) (ArityΣ ar2)
  = ArityΣ (λ x → oNestedΣArity (self (<cSize (smax-strictMono (≤ₛ-sucMono (≤ₛ-cocone _ ≤⨟ smax-≤R)) (≤ₛ-sucMono (≤ₛ-cocone _ ≤⨟ smax-≤R))))) (cod1 _) (cod2 _) reflp (ar1 _) (ar2 _))
codeMeetNested .(CΣ _ _) .(CΣ _ _) (HNeq npf) eq1 eq2 reflp (ArityΣ x) (ArityΣ x₁) with reflp ← pTrans eq1 (pSym eq2) with () ← npf reflp


codeMeetArity : ∀ {h1 h2 n}
  → (c1 c2 : ℂ ℓ )
  → (view : HeadMatchView h1 h2)
  → (eq1 : h1 ≡p codeHead c1)
  → (eq2 : h2 ≡p codeHead c2)
  → (eq3 : smax (codeSize c1) ( codeSize c2) ≡p csize)
  → HasArity n c1
  → HasArity n c2
  → HasArity n (fst (codeMeet c1 c2 view eq1 eq2 eq3))
codeMeetArity c1 c2 v eq1 eq2 eq3 ar1 ar2 with ptoc (HasArity.arEq ar1) | ptoc (HasArity.arEq ar2)
codeMeetArity (CΠ dom1 cod1) (CΠ dom2 cod2) (HEq {h1 = HΠ} reflp) _ _ reflp ar1 ar2 | reflp | reflp
  = record { arDom = _ ; arCod = _ ; arEq = reflc ; arDomAr = oNestedΣArity (self (<cSize (smax-strictMono (≤ₛ-sucMono smax-≤L) (≤ₛ-sucMono smax-≤L)))) dom1 dom2 reflp (HasArity.arDomAr ar1) (HasArity.arDomAr ar2) }
codeMeetArity (CΠ dom1 cod1) (CΠ dom2 cod2) (HNeq npf) eq1 eq2 reflp ar1 ar2 | ae1 | ae2 with reflp ← pTrans eq1 (pSym eq2) with () ← npf reflp
