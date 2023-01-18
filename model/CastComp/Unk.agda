

open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
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
open import Code
open import GTypes

module CastComp.Unk {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ} (cSize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed cSize )

  where


open SmallerCastMeet scm
open import W

unk : {{æ : Æ}} (c : ℂ ℓ) → codeSize c ≡p cSize → El c
unk CodeModule.C⁇ reflp = ⁇⁇
unk CodeModule.C℧ reflp = ℧𝟘
unk CodeModule.C𝟘 reflp = ℧𝟘
unk CodeModule.C𝟙 reflp = Gtt
unk CodeModule.Cℕ reflp = Nat⁇
unk (CodeModule.CType ⦃ inst = suc< ⦄) reflp = C⁇
unk (CodeModule.CCumul {{inst = suc<}} c) reflp = o⁇ self-1 c reflp
unk (CodeModule.CΠ dom cod) reflp = λ x →
  ⁇∈ (cod (approx x)) By StrictDecreasing (≤ₛ-cocone _ ≤⨟ smax-≤R)
  , λ _ → pure (⁇∈ (cod (approx x)) By StrictDecreasing (≤ₛ-cocone _ ≤⨟ smax-≤R))
unk (CodeModule.CΣ dom cod) reflp =
  (⁇∈ dom By StrictDecreasing smax-≤L)
  , (⁇∈ cod _ By StrictDecreasing (≤ₛ-cocone _ ≤⨟ smax-≤R))
-- The interesting case: least precise value of an equality type is the meet of the equated terms
unk (CodeModule.C≡ c x y) reflp = (c ∋ x ⊓ y approxBy StrictDecreasing ≤ₛ-refl) ⊢ x ≅ y
unk (CodeModule.Cμ tyCtor c D x) reflp = W⁇
