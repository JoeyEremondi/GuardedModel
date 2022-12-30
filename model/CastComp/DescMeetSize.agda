
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

module CastComp.DescMeetSize {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ}  (csize vsize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed csize vsize)

  where

open import Code
open import Head
open import Util


open import CastComp.DescMeet{{dt = dt}} {{dg}} {{ic}}  (⁇Allowed) {ℓ} csize vsize scm
open SmallerCastMeet scm



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

