



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

module CastComp.CastDesc {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ} (cSize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed cSize )

  where

open import Code
open import Head
open import Util
open import GTypes

open import W

open SmallerCastMeet scm
open import WMuConversion

castDesc : ∀ {{æ : Æ}} {cB1 cB2 : ℂ ℓ} {tyCtor : CName} {  sig}
  → (DS : ℂDesc cB1 sig) → (DD : ℂDesc cB2 sig)
  → (ES ED : DCtors ℓ tyCtor)
  → (b1 : ApproxEl cB1) → (b2 : ApproxEl cB2)
  → (x : ⟦ interpDesc DS b1 ⟧F  (λ æ → W̃ {{æ = æ}} (λ æ → Arg (λ d → interpDesc {{æ = æ}} (ES d) Gtt))) tt )
  → (lto : smax (descSize DS) (descSize DD) <ₛ cSize)
  → (φ : (r : ResponseD DS b1 (toApproxCommandD DS b1 (⟦_⟧F.command x)) ) → W̃ {{æ = æ}} (λ æ → Arg (λ d → interpDesc {{æ = æ}} (ED d) Gtt)) tt )
  → (φex : (IsExact æ) → (r : ResponseD DS b1 (toApproxCommandD DS b1 (⟦_⟧F.command x)) ) → LÆ (W̃ {{æ = æ}} (λ æ → Arg (λ d → interpDesc {{æ = æ}} (ED d) Gtt)) tt ))
  → LÆ ( ⟦ interpDesc DD b2 ⟧F  (λ æ → W̃ {{æ = æ}} (λ æ → Arg (λ d → interpDesc {{æ = æ}} (ED d) Gtt))) tt )
castDesc CEnd CEnd ES ED b1 b2 (FC com resp respEx) lto φ φex = pure (FC com (λ ()) (λ _ ()))
castDesc (CArg cS _ DS _ reflp) (CArg cD _ DD _ reflp) ES ED b1 b2 (FC (a , com) resp respEx) lto φ φex = do
  aD ← ⟨ cD b2 ⇐ cS b1 ⟩ a
    By Decreasing ≤< (smax-mono
      (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0) ≤⨟ ≤↑ _)
      (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0) ≤⨟ ≤↑ _)) lto
  let
    transportResp : _ → _
    transportResp r = substPath (λ x → ResponseD DS (b1 , fst x) (snd x)) (symPath (toApproxCommandArg cS _ DS _ reflp b1 a com)) r
  (FC comD respD respExD) ← castDesc DS DD ES ED (b1 , approx a) (b2 , approx aD)
    (FC com
      (λ r → resp (transportResp r))
      λ pf r → respEx pf (transportResp r) )
    (≤< (smax-mono (smax*-≤-n (FLit 1) ≤⨟ ≤↑ _) (smax*-≤-n (FLit 1) ≤⨟ ≤↑ _)) lto)
    (λ r → φ (transportResp r))
    λ pf r → φex pf (transportResp r)
  let
    transportResp' : _ → _
    transportResp' r = substPath (λ x → ResponseD DD (b2 , fst x) (snd x)) ( (toApproxCommandArg cD _ DD _ reflp b2 aD comD)) r
  pure (FC (aD , comD) (λ r → respD (transportResp' r)) λ pf r → respExD pf (transportResp' r))
castDesc (CRec cS x₁ DS cB' reflp) (CRec cD x₃ DD cB'' reflp) ES ED b1 b2 (FC com resp respEx) lto φ φex = do
  let
    transportResp : _ → _
    transportResp r = substPath (λ x → ResponseD DS b1 x) (symPath (toApproxCommandRec cS _ DS _ reflp b1 com)) r
  (FC comD respD respExD) ← castDesc DS DD ES ED b1 b2
    (FC com
      (λ r → resp (Rest (transportResp r)))
      λ pf r → respEx pf (Rest (transportResp r)) )
    (≤< (smax-mono (smax*-≤-n (FLit 1) ≤⨟ ≤↑ _) (smax*-≤-n (FLit 1) ≤⨟ ≤↑ _)) lto)
    (λ r → φ (Rest (transportResp r)))
    λ pf r → φex pf (Rest (transportResp r))
  let
    transportResp' : _ → _
    transportResp' r = substPath (λ x → ResponseD DD b2 x) ((toApproxCommandRec cD _ DD _ reflp b2 comD)) r
    recFun : (r : _) → _
    recFun r = approxμ _ _ _ _ (φ (Rec (exact (⟨ cS b1 ⇐ cD b2 ⟩ approx r
           approxBy Decreasing ≤<  (smax-commut _ _ ≤⨟ (smax-mono
                (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0) ≤⨟ ≤↑ _)
                (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0) ≤⨟ ≤↑ _))) lto))))
    recFunEx : IsExact _ → (r : _) → _
    recFunEx pf r = do
      rCast ← (⟨ cS b1 ⇐ cD b2 ⟩ r
           By Decreasing ≤<  (smax-commut _ _ ≤⨟ (smax-mono
                (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0) ≤⨟ ≤↑ _)
                (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0) ≤⨟ ≤↑ _))) lto)
      φex pf (Rec rCast)
  pure (FC comD
    (λ {(Rec r) → recFun r ; (Rest r) → respD (transportResp' r)})
    (λ pf → λ {(Rec r) → recFunEx pf r ; (Rest r) → respExD  pf (transportResp' r)})
    )
