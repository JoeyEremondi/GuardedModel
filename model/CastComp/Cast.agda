


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

module CastComp.Cast {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ} (cSize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed cSize )

  where

open import Code
open import Head
open import Util
open import GTypes

open import W

open SmallerCastMeet scm
open import WMuConversion


cast : ∀ {{æ : Æ}} {h1 h2}
  → (c1 c2 : ℂ ℓ )
  → El c1
  → (view : HeadMatchView h1 h2)
  → (eq1 : h1 ≡p codeHead c1)
  → (eq2 : h2 ≡p codeHead c2)
  → (smax (codeSize c1) ( codeSize c2) ≡p cSize)
  → LÆ (El c2)
-- Casting to ℧, from ℧, or between mismatched types is an error
cast c1 c2 x (H℧L x₁) eq1 eq2 reflp = pure (℧ c2)
cast c1 c2 x (H℧R x₁) eq1 eq2 reflp = pure (℧ c2)
cast c1 c2 x (HNeq x₁) eq1 eq2 reflp = pure (℧ c2)
-------------------------------------------------------
-- Casting from ⁇
-- ---------------------------------------------------
-- ⁇ or ℧ in type ⁇ produce ⁇ and ℧ respectively
cast C⁇ c2 ⁇⁇ (H⁇L reflp x₂) eq1 eq2 reflp = {!!}
cast C⁇ c2 ⁇℧ (H⁇L  reflp x₂) eq1 eq2 reflp = pure (℧ c2)
cast C⁇ c2 (⁇Tag {h = h} x) (H⁇L {h2 = HStatic h2} reflp x₂) eq1 eq2 reflp with headDecEq h h2
... | no neq = pure (℧ c2)
cast C⁇ C𝟙 (⁇Tag {h = .H𝟙} ⁇𝟙) (H⁇L {_} {.(HStatic _)} reflp x₂) eq1 eq2 reflp | yes reflp = {!!}
cast C⁇ Cℕ (⁇Tag {h = .Hℕ} (⁇ℕ x)) (H⁇L {_} {.(HStatic _)} reflp x₂) eq1 eq2 reflp | yes reflp = {!!}
cast C⁇ CType (⁇Tag {h = .HType} (⁇Type x)) (H⁇L {_} {.(HStatic _)} reflp x₂) eq1 eq2 reflp | yes reflp = {!!}
cast C⁇ (CCumul x) (⁇Tag {h = .HCumul} (⁇Cumul c x₁)) (H⁇L {_} {.(HStatic _)} reflp x₂) eq1 eq2 reflp | yes reflp = {!!}
cast C⁇ (CΠ c2 cod) (⁇Tag {h = .HΠ} (⁇Π x x₁)) (H⁇L {_} {.(HStatic _)} reflp x₂) eq1 eq2 reflp | yes reflp = {!!}
cast C⁇ (CΣ c2 cod) (⁇Tag {h = .HΣ} (⁇Σ x)) (H⁇L {_} {.(HStatic _)} reflp x₂) eq1 eq2 reflp | yes reflp = {!!}
cast C⁇ (C≡ c2 x y) (⁇Tag {h = .H≅} (⁇≡ x₁)) (H⁇L {_} {.(HStatic _)} reflp x₂) eq1 eq2 reflp | yes reflp = {!!}
cast C⁇ (Cμ tyCtor c2 D x) (⁇Tag {h = .(HCtor _)} (⁇μ d x₁ x₃)) (H⁇L {_} {.(HStatic _)} reflp x₂) eq1 eq2 reflp | yes reflp = {!!}
cast C⁇ c2 (⁇Tag {h = h} x) (H⁇L {h2 = h2} reflp x₂) eq1 eq2 reflp = {!!}
-- Casting to ⁇
cast C𝟘 C⁇ x (H⁇R reflp) eq1 eq2 reflp = {!!}
cast C𝟙 C⁇ x (H⁇R reflp) eq1 eq2 reflp = {!!}
cast Cℕ C⁇ x (H⁇R reflp) eq1 eq2 reflp = {!!}
cast CType C⁇ x (H⁇R reflp) eq1 eq2 reflp = {!!}
cast (CCumul x₁) C⁇ x (H⁇R reflp) eq1 eq2 reflp = {!!}
cast (CΠ c1 cod) C⁇ x (H⁇R reflp) eq1 eq2 reflp = {!!}
cast (CΣ c1 cod) C⁇ x (H⁇R reflp) eq1 eq2 reflp = {!!}
cast (C≡ c1 x₁ y) C⁇ x (H⁇R reflp) eq1 eq2 reflp = {!!}
cast (Cμ tyCtor c1 D x₁) C⁇ x (H⁇R reflp) eq1 eq2 reflp = {!!}
-- Casting between types with the same head

cast C𝟙 C𝟙 x (HEq {h1 = H𝟙} reflp) eq1 eq2 reflp = pure x
cast C𝟘 C𝟘 x (HEq {h1 = H𝟘} reflp) eq1 eq2 reflp = pure x
cast Cℕ Cℕ x (HEq {h1 = Hℕ} reflp) eq1 eq2 reflp = pure x
cast CType CType x (HEq {h1 = HType} reflp) eq1 eq2 reflp = pure x
cast (CΠ c1 cod) (CΠ c2 cod₁) f (HEq {h1 = HΠ} reflp) eq1 eq2 reflp
  = pure (λ x → fAppr x , fExact x)
    where
      fAppr : (x : {!!}) → {!!}
      fExact : (x : {!!}) → {!!}
cast (CΣ c1 cod) (CΣ c2 cod₁) x (HEq {h1 = HΣ} reflp) eq1 eq2 reflp = {!!}
cast (C≡ c1 x₁ y) (C≡ c2 x₂ y₁) x (HEq {h1 = H≅} reflp) eq1 eq2 reflp = {!!}
cast (CCumul x₁) (CCumul x₂) x (HEq {h1 = HCumul} reflp) eq1 eq2 reflp = {!!}
cast (Cμ tyCtor c1 D x₁) (Cμ tyCtor₁ c2 D₁ x₂) x (HEq {h1 = HCtor x₃} reflp) eq1 eq2 reflp = {!!}
