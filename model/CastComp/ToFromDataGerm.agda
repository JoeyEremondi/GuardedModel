


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

module CastComp.ToFromDataGerm {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ} (cSize : Size)  (scm : SmallerCastMeet ℓ ⁇Allowed cSize )

  where

open import Head
open import Util
open import GTypes

open import W

open SmallerCastMeet scm
open import WMuConversion
open import Cubical.Foundations.Isomorphism


open import Code

open import CastComp.CastCommandResp ⁇Allowed cSize scm

-- Helper function to take the field-by-field meet for a constructor
descElToGermAppr : ∀ {{æ : Æ}} {cB : ℂ ℓ} {tyCtor : CName} { skel}
      → (D : ℂDesc  cB skel)
      → (DG : GermCtor skel)
      → (isCode : GermCtorIsCode ℓ DG)
      → (E : DCtors ℓ tyCtor)
      → (b : ApproxEl cB)
      → (x : ⟦ interpDesc D b ⟧F  (λ æ → W̃ {{æ = æ}} (λ æ → Arg (λ d → interpDesc {{æ = æ}} (E d) Gtt))) tt )
      → (lto : descSize D <ₛ cSize)
      → (ltB : codeSize cB <ₛ cSize)
      → (φ : (r : ResponseD D b (toApproxCommandD D b (⟦_⟧F.command x)) ) → ⁇Ty ℓ )
      → ((r : GermResponse DG) → ⁇Ty ℓ)
descElToGermAppr (CodeModule.CArg c x₁ D cB' x₂) (GArg A DG) (GArgCode cr cIso rest) E b (FC (a , com) resp respEx) lto ltB φ (inl r) =
  let
    rCast = ⟨ {!!} ⇐ cr ⟩ approx (Iso.fun cIso r) approxBy {!!}
    respR = resp {!!}
  in {!!}
descElToGermAppr (CodeModule.CArg c x₁ D cB' x₂) (GArg A DG) (GArgCode cr cIso rest) E b (FC (a , com) resp respEx) lto ltB φ (inr r) =
  descElToGermAppr D DG rest E (b , approx a) (FC com (λ rr → resp {!!}) {!!}) {!!} {!!} {!!} r
descElToGermAppr (CodeModule.CRec c x₁ D cB' x₂) (GRec A DG) isCode E b x lto ltB φ r = {!!}

-- -- Meets for members of inductive types
-- descMuMeet : ∀ {{æ : Æ}} {tyCtor : CName}
--       → (Ds : DCtors ℓ tyCtor)
--       → (x y : W̃ (λ æ → Arg (λ d → interpDesc {{æ = æ}} (Ds d) Gtt)) tt  )
--       → (lto : ∀ {d} → descSize (Ds d) <ₛ cSize)
--       → (lto' : S1 <ₛ cSize)
--       → LÆ (W̃ (λ æ → Arg (λ d → interpDesc {{æ = æ}} (Ds d) Gtt)) tt  )
-- descMuBindMeet : ∀ {{æ : Æ}} {tyCtor : CName}
--       → (Ds : DCtors ℓ tyCtor)
--       → (x y : LÆ (W̃ (λ æ → Arg (λ d → interpDesc {{æ = æ}} (Ds d) Gtt)) tt)  )
--       → (lto : ∀ {d} → descSize (Ds d) <ₛ cSize)
--       → (lto' : S1 <ₛ cSize)
--       → LÆ (W̃ (λ æ → Arg (λ d → interpDesc {{æ = æ}} (Ds d) Gtt)) tt  )

-- descMuMeet Ds W℧ y lto lto' = pure W℧
-- descMuMeet Ds x W℧ lto lto' = pure W℧
-- descMuMeet Ds W⁇ y lto lto' = pure y
-- descMuMeet Ds x W⁇ lto lto' = pure x
-- descMuMeet {{æ = æ}} Ds (Wsup (FC (d , com1) resp1 exact1)) (Wsup (FC (d2 , com2) resp2 exact2)) lto lto' with decFin d d2
-- ... | no neq = pure W℧
-- ... | yes reflp = do
--   -- We need to convince Agda that unit meet with itself is itself
--   let 𝟙eq = oMeet𝟙 (self (<cSize lto'))
--   -- Compute the helper function that lets us call ourselves recursively in descElMeet
--   let φ = λ r1 r2 → fromL (descMuMeet ⦃ æ = Approx ⦄ Ds (resp1 r1) (resp2 r2) lto lto')
--   let φEx = λ pf r1 r2 → descMuBindMeet Ds (exact1 pf r1) (exact2 pf r2) lto lto'

--   -- λ r1 r2 → descMuMeet Ds (resp1 r1) (resp2 r2) lto lto'
--   (FC com𝟙𝟙 resp𝟙𝟙 exact𝟙𝟙) ← descElMeet (Ds d) Ds Gtt Gtt (FC com1 resp1 exact1) (FC com2 resp2 exact2)
--     lto
--     lto'
--     φ
--     φEx
--   let comRet = substPath (CommandD (Ds d)) 𝟙eq com𝟙𝟙
--   let respRet = λ r → resp𝟙𝟙 (transport (cong₂ (ResponseD (Ds d)) (sym 𝟙eq) (congP₂ (λ i x y → toApproxCommandD (Ds d) x y) _ (symP (subst-filler _ _ com𝟙𝟙))) ) r)
--   let exactRet = λ pf r → exact𝟙𝟙 pf (transport (cong₂ (ResponseD (Ds d)) (sym 𝟙eq) (congP₂ (λ i x y → toApproxCommandD (Ds d) x y) _ (symP (subst-filler _ _ com𝟙𝟙))) ) r)
--   pure (Wsup (FC (d , comRet) respRet exactRet ))

-- descMuBindMeet Ds (Later x) y lto lto' = Later λ tic → descMuBindMeet Ds (x tic) y lto lto'
-- descMuBindMeet Ds x (Later y)  lto lto' = Later λ tic → descMuBindMeet Ds x (y tic) lto lto'
-- descMuBindMeet Ds (Now x) (Now y)  lto lto' = descMuMeet Ds x y lto lto'
