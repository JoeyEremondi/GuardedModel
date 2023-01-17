
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
open import GuardedModality as G
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import ApproxExact
open import InductiveCodes
open import Sizes
-- open import CodePair

open import CastComp.Interface

module CastComp.FromGerm {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ} (cSize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed cSize )

  where

open import Code
open import Head
open import Util
open import GTypes

open import W

open SmallerCastMeet scm
open import WMuConversion

fromGerm : ∀ {{æ : Æ}} {h} (c : ℂ ℓ) → (x : ⁇GermTy ℓ h)
  → codeHead c ≡p HStatic h
  → codeSize c ≡p cSize
  → LÆ (El c)
fromGerm C𝟙 ⁇𝟙 peq reflp = pure Gtt
fromGerm Cℕ (⁇ℕ x) peq reflp = pure x
fromGerm CType (⁇Type x) peq reflp = pure x
fromGerm (CCumul {{inst = suc<}} cTo) (⁇Cumul cFrom x) peq reflp =
  oCast (self-1 {{inst = suc<}} ) cFrom cTo x reflp
fromGerm {{æ = Approx}} (CΠ dom cod) (⁇Π f _) peq reflp =
  pure {{æ = Approx}} λ x → ⟨ cod x ⇐ C⁇ ⟩ (f tt)
             ------------------------------------------------------------------
             approxBy Decreasing ≤ₛ-sucMono (codeMaxL (cod x)  ≤⨟ ≤ₛ-cocone x ≤⨟ smax-≤R)
    , λ ()
fromGerm {{æ = Exact}} (CΠ dom cod) (⁇Π fAppr fExact) peq reflp =
  Now λ x →
    toExact _ ( ⟨ cod (toApprox _ x) ⇐ C⁇ ⟩ (fAppr tt)
      ----------------------------------------------------------------------
      approxBy Decreasing ≤ₛ-sucMono (codeMaxL _  ≤⨟ ≤ₛ-cocone _ ≤⨟ smax-≤R))
    , λ _ →  do
        xCast ← [ Exact ]⟨ C⁇ ⇐ dom ⟩ x
          -----------------------------------------
          By Decreasing ≤ₛ-sucMono (codeMaxR _ ≤⨟  smax-≤L)
        let ▹x = G.next xCast
        fx ← fExact isExact (transport (symPath (⁇Wrap≡ {{æ = Exact}})) ▹x)
        [ Exact ]⟨ cod (toApprox _ x) ⇐ C⁇ ⟩ fx By Decreasing {!!}
fromGerm (CΣ dom cod) (⁇Σ (x , y)) peq reflp = do
  xRet ← ⟨ dom ⇐ C⁇ ⟩ x
    By Decreasing {!!}
  yRet ← ⟨ cod (approx xRet) ⇐ C⁇ ⟩ y
    By Decreasing {!!}
  pure (xRet , yRet)
fromGerm (C≡ c x y) (⁇≡ (wit ⊢ .⁇⁇ ≅ .⁇⁇)) peq reflp = do
  castWit ← ⟨ c ⇐ C⁇ ⟩ wit
    By Decreasing {!!}
  let
    upperBound = c ∋ x ⊓ y
                 approxBy Decreasing {!!}
  let
    retWit = c ∋ approx castWit ⊓ upperBound
      approxBy Decreasing {!!}
  pure (retWit ⊢ x ≅ y)
fromGerm (Cμ tyCtor c D x) (⁇μ d x₁ x₂) peq reflp = {!!}
