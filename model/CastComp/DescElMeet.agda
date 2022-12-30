


-- Bound on the size of the meet on codes, assuming we have meet, cast, etc. for smaller types


open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import DecPEq
open import Cubical.Data.Nat
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
open import Cubical.Foundations.Isomorphism

open import ApproxExact
open import InductiveCodes
open import Sizes
-- open import CodePair

open import CastComp.Interface

module CastComp.DescElMeet {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ} (cSize : Size) (vSize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed cSize vSize)

  where

open import Code
open import Head
open import Util
open import GTypes

open import W

open SmallerCastMeet scm
open import WMuConversion






descElMeet : ∀ {{æ : Æ}} {cB cBTarget : ℂ ℓ} {tyCtor skel oTop}
      → (D : ℂDesc  cB skel)
      → (E : DCtors ℓ tyCtor)
      → (b : ApproxEl cB)
      → (x y : ℂDescEl D (ℂμ tyCtor E) b )
      → (lto : oTop <ₛ cSize )
      → (ltB : (codeSize cBTarget ≤ₛ (codeSize cB) ))
      → (lt : descSize D ≤ₛ  oTop)
      → LÆ (ℂDescEl D (ℂμ tyCtor E) b)
descElMeet CEnd E b ElEnd ElEnd lto ltB lt = pure ElEnd
descElMeet (CArg c x D .(CΣ _ c) .reflp) E b (ElArg a1 rest1) (ElArg a2 rest2) lto ltB lt = do
  pure (ElArg {!!} {!!})
descElMeet (CRec c x D .(CΣ _ c) .reflp) E b (ElRec f1 rest1) (ElRec f2 rest2) lto ltB lt = do
  pure (ElRec ? ?)
