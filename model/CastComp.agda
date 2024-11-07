
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Sum
import Cubical.Data.Empty as Empty
open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
-- open import Cubical.Data.Equality
open import UnkGerm
open import GuardedAlgebra
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation.Properties as Prop

open import ApproxExact
open import InductiveCodes
open import Sizes
open import Constructors
open import GTypes

module CastComp {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}   where


open import CastComp.Interface
open import CastComp.CodeMeet
open import CastComp.Meet
open import CastComp.Cast
open import CastComp.Unk
open import CastComp.CodeMeetArity

open import Head

castCompRec : ∀ {ℓ} {size} → SizedCastMeet ℓ true size
castCompRec = FixCastMeet helper _ true _
  where
    helper : (∀ { ℓ ⁇Allowed csize} → SmallerCastMeet ℓ ⁇Allowed csize → SizedCastMeet ℓ ⁇Allowed csize )
    helper {ℓ = ℓ} {⁇Allowed = al} {csize = cs} scm = record
                   { o⁇ = unk al _ scm
                   ; oMeet = meet al cs scm
                   ; oMeet𝟙 = reflc
                   ; oCodeMeet = λ c1 c2 pf → fst (codeMeet al cs scm c1 c2 (headMatchView (codeHead c1) (codeHead c2)) reflp reflp pf)
                   ; oCodeMeetSize = λ c1 c2 pf → subst (λ x → codeSize (fst (codeMeet al cs scm c1 c2 (headMatchView _ _) reflp reflp pf)) ≤ₛ x) (symPath (ctop pf))  (snd (codeMeet al cs scm c1 c2 (headMatchView _ _) reflp reflp pf))
                   ; oCodeMeetArity = λ c1 c2 pf a1 a2 → codeMeetArity al cs scm c1 c2 (headMatchView _ _) reflp reflp pf a1 a2
                   ; oNestedΣArity = λ c1 c2 pf a1 a2 → codeMeetNested al cs scm c1 c2 (headMatchView _ _) reflp reflp pf a1 a2
                   ; oCast = λ cS cD x pf → cast al cs scm cS cD x (headMatchView _ _) reflp reflp pf
                   }
