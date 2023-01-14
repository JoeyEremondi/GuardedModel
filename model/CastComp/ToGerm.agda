
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

module CastComp.ToGerm {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ} (cSize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed cSize )

  where

open import Code
open import Head
open import Util
open import GTypes

open import W

open SmallerCastMeet scm
open import WMuConversion

toGerm : ∀ {{æ : Æ}} {h} (c : ℂ ℓ) → (x : El c) → codeHead c ≡p HStatic h → codeSize c ≡p cSize → LÆ (⁇Ty ℓ)
toGerm C𝟘 x peq ceq = pure ⁇℧
toGerm C𝟙 Gtt peq ceq = pureTag ⁇𝟙
toGerm C𝟙 ℧𝟙 peq ceq = pure ⁇℧
toGerm Cℕ x peq ceq = pureTag (⁇ℕ x)
toGerm CType x peq ceq = pureTag (⁇Type x)
toGerm (CCumul c) x peq ceq = pureTag (⁇Cumul c x )
toGerm (CΠ dom cod) f peq ceq =
  pureTag (⁇Π (λ _ → fAppr) fExact)
    where
    fAppr  =
      let
        f⁇ = fst (f (⁇∈ dom By {!!}))
      in ⟨ C⁇ ⇐ cod _ ⟩ (approx f⁇) approxBy Decreasing {!!}
    fExact : _ → (x : _) → _
    fExact pf x = do
      xRaw ← θ pf (transport ⁇Wrap≡ x)
      xCast ← ⟨ dom ⇐ C⁇ ⟩ xRaw By Decreasing {!!}
      fx ← snd (f xCast) pf
      ⟨ C⁇ ⇐ cod (approx xCast) ⟩ fx By Decreasing {!!}
toGerm (CΣ dom cod) (x , y) peq ceq = do
  x⁇ ← ⟨ C⁇ ⇐ dom ⟩ x By Decreasing {!!}
  y⁇ ← ⟨ C⁇ ⇐ cod (approx x) ⟩ y By Decreasing {!!}
  pureTag (⁇Σ (x⁇ , y⁇))
toGerm (C≡ c x₁ y) (wit ⊢ _ ≅ _) peq ceq =
  let
    retWit = ⟨ C⁇ ⇐ c ⟩ wit approxBy {!!}
  in pureTag (⁇≡ ((exact retWit) ⊢ ⁇⁇ ≅ ⁇⁇))
toGerm (Cμ tyCtor c D x₁) x peq ceq = {!!}
