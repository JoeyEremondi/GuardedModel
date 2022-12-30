

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
    (⁇Allowed : Bool) {ℓ}  (csize vsize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed csize vsize)

  where

open import Code
open import Head
open import Util


open import CastComp.DescMeet {{dt = dt}} {{dg}} {{ic}}  (⁇Allowed) {ℓ} csize vsize scm
open import CastComp.CodeMeet {ℓ} (⁇Allowed) csize vsize scm
open SmallerCastMeet scm

open import CastComp.CodeMeetSize {ℓ} (⁇Allowed) csize vsize scm


codeMeetArity : ∀ {h1 h2 h n}
  → (c1 c2 : ℂ ℓ )
  → (view : HeadMatchView h1 h2)
  → (eq1 : h1 ≡p codeHead c1)
  → (eq2 : h2 ≡p codeHead c2)
  → (eq3 : smax (codeSize c1) ( codeSize c2) ≡p csize)
  → HasArity h n c1
  → HasArity h n c2
  → HasArity h n (codeMeet c1 c2 view eq1 eq2 eq3)
