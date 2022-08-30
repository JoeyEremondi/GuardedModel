

-- Bound on the size of the meet on codes, assuming we have meet, cast, etc. for smaller types


open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
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
open import Ord

open import CastComp.Interface

module CastComp.Unk {{dt : DataTypes}} {{dg : DataGerms}} {{ic : InductiveCodes}} {{dgs : DataGermsSmaller}}
    {ℓ} (cSize : Ord) (vSize : Ord) (scm : SmallerCastMeet ℓ cSize vSize)

  where

open import Code
open import Head
open import Util


open SmallerCastMeet scm

⁇ : ∀ {{æ : Æ}}  → (c : ℂ ℓ)
      → (pfc1 : codeSize c ≡p cSize )
      → ( pfv2 : OZ ≡p vSize )
      → (El c)

⁇ C⁇ reflp reflp = ⁇⁇
⁇ C℧ reflp reflp = tt
⁇ C𝟘 reflp reflp = tt
⁇ C𝟙 reflp reflp = true
⁇ (CType {{suc<}}) reflp reflp = C⁇
⁇ (CCumul {{suc<}} x) reflp reflp = o⁇ ℓself x reflp reflp
⁇ (CΠ dom cod) reflp reflp x = ⁇ cod (approx x)
  By hide {arg = ≤o-sucMono (≤o-cocone ⦃ æ = Approx ⦄ _ _ (omax∞-self _) ≤⨟ omax-≤R ≤⨟ omax∞-self _ ≤⨟ omax∞-distR)}
⁇ (CΣ dom cod) reflp reflp =
  withApprox (λ æ' → [ æ' ]⁇ dom
    By hide {arg = ≤o-sucMono (omax∞-self _ ≤⨟ omax-≤L)}) ,
  ⁇ cod _
    By hide {arg = ≤o-sucMono (≤o-cocone ⦃ æ = Approx ⦄ _ _ (omax∞-self _) ≤⨟ omax-≤R ≤⨟ omax∞-self _ ≤⨟ omax∞-distR)}
⁇ (C≡ c x y) reflp reflp =
  wit ⊢ x ≅ y
   where
     wit = fromL (
       [ Approx ] c ∋ x ⊓ y
         By hide {arg = ≤o-sucMono (omax∞-self _)})
⁇ (Cμ tyCtor c D x) reflp reflp = W⁇
