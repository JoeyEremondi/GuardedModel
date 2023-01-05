


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

module CastComp.CastCommandResp {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ} (cSize : Size) (vSize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed cSize vSize)

  where

open import Head
open import Util
open import GTypes

open import W

open SmallerCastMeet scm
open import WMuConversion


open import Code

castCommand : ∀ {{æ : Æ}} {cB : ℂ ℓ} {skel}
  → (D : ℂDesc cB skel)
  → (b1 b2 : ApproxEl cB)
  → (lt : descSize D <ₛ cSize)
  → (x : CommandD D b1)
  → LÆ (CommandD D b2)
castCommand CodeModule.CEnd b1 b2 lt x = pure tt
castCommand (CodeModule.CArg c x₁ D cB' reflp) b1 b2 lt (a , com) = do
  a' ← ⟨ c b2 ⇐ c b1 ⟩ a By Decreasing ≤< (smax-lub (≤ₛ-cocone b1 ≤⨟ smax*-≤-n Fin.zero) (≤ₛ-cocone b2 ≤⨟ smax*-≤-n Fin.zero) ≤⨟ ≤↑ _ ) lt
  com' ← castCommand D _ _ (≤< (smax*-≤-n (FLit 1) ≤⨟ ≤↑ _) lt) com
  pure (a' , com')
castCommand (CodeModule.CRec c x₁ D cB' reflp) b1 b2 lt com = castCommand D b1 b2 (≤< (smax*-≤-n (FLit 1) ≤⨟ ≤↑ _) lt) com

castResponse : ∀ {{æ : Æ}} {cB : ℂ ℓ} {skel}
  → (D : ℂDesc cB skel)
  → (b1 b2 : ApproxEl cB)
  → (lt : descSize D <ₛ cSize)
  → (com1 : CommandD {{æ = Approx}} D b1)
  → (com2 : CommandD {{æ = Approx}} D b2)
  → ResponseD D b1 com1
  → LÆ (ResponseD D b2 com2)
castResponse (CodeModule.CArg c x D cB' reflp) b1 b2 lt com1 com2 r =
  castResponse D _ _ (≤< (smax*-≤-n (FLit 1) ≤⨟ ≤↑ _) lt) (snd com1) (snd com2) r
castResponse (CodeModule.CRec c x D cB' reflp) b1 b2 lt com1 com2 (Rec x₂) = do
  ret ← ⟨ c b2 ⇐ c b1 ⟩ x₂ By Decreasing ≤< (smax-lub ((≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)) ≤⨟ ≤↑ _) ((≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)) ≤⨟ ≤↑ _)) lt
  pure (Rec ret)
castResponse (CodeModule.CRec c x D cB' reflp) b1 b2 lt com1 com2 (Rest x₂) = do
  ret ← castResponse D b1 b2 (≤< (smax*-≤-n (FLit 1) ≤⨟ ≤↑ _) lt) com1 com2 x₂
  pure (Rest ret)
