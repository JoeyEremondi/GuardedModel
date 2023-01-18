


-- Bound on the size of the meet on codes, assuming we have meet, cast, etc. for smaller types


open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.Base
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

-- Taken from Agda cubical library, it's in the newest version but I need to update
decRec : ∀ {ℓ ℓ'} {P : Type ℓ} {A : Type ℓ'} → (P → A) → (¬ P → A) → (Dec P) → A
decRec ifyes ifno (yes p) = ifyes p
decRec ifyes ifno (no ¬p) = ifno ¬p


arityDom≤ : ∀ {ℓ} {c : ℂ ℓ} {n } → (ar : HasArity n c) → codeSize (HasArity.arDom ar) <ₛ codeSize c
arityCod≤ : ∀ {ℓ} {c : ℂ ℓ} {n } → (ar : HasArity n c) → {x : ApproxEl (HasArity.arDom ar)} -> codeSize (HasArity.arCod ar x) <ₛ codeSize c

arityDom≤ ar = substPath (λ x → _ <ₛ codeSize x) (sym (HasArity.arEq ar)) (≤ₛ-sucMono smax-≤L)
arityCod≤ ar = substPath (λ x → _ <ₛ codeSize x) (sym (HasArity.arEq ar)) (≤ₛ-sucMono (≤ₛ-cocone _ ≤⨟ smax-≤R))

-- castTeleFromGerm :  ∀ {n} ->  (A : GermTele n) →


-- Helper function to take the field-by-field meet for a constructor
descElToGerm : ∀ {{æ : Æ}} {cB : ℂ ℓ} {tyCtor : CName} { skel}
      → (D : ℂDesc  cB skel)
      → (DG : GermCtor skel)
      → (isCode : GermCtorIsCode ℓ DG)
      → (E : DCtors ℓ tyCtor)
      → (b : ApproxEl cB)
      → (x : ⟦ interpDesc D b ⟧F  (λ æ → W̃ {{æ = æ}} (λ æ → Arg (λ d → interpDesc {{æ = æ}} (E d) Gtt))) tt )
      → (lto : descSize D <ₛ cSize)
      → (φ : (r : ResponseD D b (toApproxCommandD D b (⟦_⟧F.command x)) ) → ⁇Ty ℓ )
      → (φex : (IsExact æ) → (r : ResponseD D b (toApproxCommandD D b (⟦_⟧F.command x)) ) → LÆ (⁇Ty ℓ) )
      → ((r : GermResponse DG) → ⁇Ty ℓ × (IsExact æ → LÆ (⁇Ty ℓ)))
-- Inl case: Given our response, translate it into a response that is the argument type a takes
-- since a must be a function (possibly with argument  type 𝟙)
-- Then generate a value of type ⁇ from the return of a
descElToGerm {{æ = æ}} (CodeModule.CArg c ar D cB' reflp) (GArg A DG) (GArgCode cr cIso rest) E b (FC (a , com) resp respEx) lto φ φex (inl r)  =
  let
    -- Two cases: either this is our first time traversing  into the LHS of part of the germ, it's not.
    -- If it is, call ourselves recursively with but set the flag
    -- Otherwise, this case is impossible (violates strict positivity)
    -- but we need to return something, so we return an error
    rCast = decRec
      (λ pf → fromL (oCast (selfGermNeg (ptoc pf)) {{æ = Approx}} cr (HasArity.arDom (ar b)) (approx (Iso.fun cIso r)) reflp) )
      (λ _ → ℧Approx (HasArity.arDom (ar b)))
      (⁇Allowed ≟ true)
    -- if ⁇Allowed
    --   then fromL (oCast {!!} {{æ = Approx}} {!!} {!!} {!!} {!!})
    --   else ℧Approx (HasArity.arDom (ar b))
    -- ⟨ HasArity.arDom (ar b) ⇐ cr ⟩ approx (Iso.fun cIso r)
    --   approxBy Decreasing <≤ (≤ₛ-sucMono (smax-lub {!!} {!!})) lto
    aFun = transport (congPath (λ c → ÆEl c _) (HasArity.arEq (ar b))) a
    aRet  = (fst (aFun (exact rCast)))
    ⁇Ret = ⟨ C⁇ ⇐ HasArity.arCod (ar b) _ ⟩ approx aRet
         approxBy Decreasing ≤< (codeMaxR _ ≤⨟ <-in-≤ (arityCod≤ (ar b)) ≤⨟ ≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0) ≤⨟ ≤↑ _ ) lto
    exComp = λ pf → do
      rCastEx ← decRec
        (λ pf → (oCast (selfGermNeg (ptoc pf))  cr (HasArity.arDom (ar b)) (Iso.fun cIso r) reflp) )
        (λ _ → pure ( ℧ (HasArity.arDom (ar b))))
        (⁇Allowed ≟ true)
      aRetEx ← snd (aFun rCastEx) pf
      ⟨ C⁇ ⇐ HasArity.arCod (ar b) (approx rCastEx) ⟩ aRetEx
        By Decreasing (≤< (codeMaxR _ ≤⨟ <-in-≤ (arityCod≤ (ar b)) ≤⨟ ≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0) ≤⨟ ≤↑ _ ) lto)
      -- aRetEx ← snd (aFun rCastEx) pf
      -- ⟨ C⁇ ⇐ HasArity.arCod (ar b) rCast ⟩ aRet By {!!}
  in  exact {c = C⁇} ⁇Ret , exComp
-- Inr case : recur on the rest of the fields
descElToGerm {{æ = æ}} (CodeModule.CArg c ar D cB' reflp) (GArg A DG) (GArgCode cr cIso rest) E b (FC (a , com) resp respEx) lto φ φex (inr r) = let
    transportResp : (rr : _) → _
    transportResp = λ rr → (transport (congPath (λ x → ResponseD D (b , fst x) (snd x)) (sym (toApproxCommandArg c ar D cB' reflp b a com) )) rr)
    recResp = λ rr → resp (transportResp rr)
    recRespEx = λ pf rr → respEx pf (transportResp rr)
    φrec = λ rr → φ (transportResp rr)
    φrecEx = λ pf rr → φex pf (transportResp rr)
  in
    descElToGerm D DG rest E (b , approx a) (FC com recResp recRespEx)
      (≤< (smax*-≤-n (FLit 1) ≤⨟ ≤↑ _) lto)
      φrec
      φrecEx
      r
-- Inl case: generate a value of type ⁇ from the recursive value of the datatype in the input,
-- by converting the Germ response into a response for the datatype
descElToGerm (CodeModule.CRec c ar D cB' x₂) (GRec A DG) (GRecCode cr cIso rest) E b x lto φ φex (inl r) =
  let
    rCast = decRec
      (λ pf → fromL (oCast (selfGermNeg (ptoc pf)) {{æ = Approx}} cr (c b) (approx (Iso.fun cIso r)) reflp) )
      (λ _ → ℧Approx (c b))
      (⁇Allowed ≟ true)
    ⁇Ret = φ (Rec (exact rCast))
    exComp = λ pf → do
      rCastEx ← decRec
        (λ pf → (oCast (selfGermNeg (ptoc pf))  cr (c b) (Iso.fun cIso r) reflp) )
        (λ _ → pure ( ℧ (c b)))
        (⁇Allowed ≟ true)
      φex pf (Rec rCastEx)
  in  ⁇Ret , exComp
-- Inr case : recur on the rest of the fields
descElToGerm (CodeModule.CRec c x₁ D cB' reflp) (GRec A DG) (GRecCode cr cIso rest) E b (FC com resp respEx) lto φ φex (inr r) = let
    transportResp : (rr : _) → _
    transportResp = λ rr → Rest (transport (congPath (ResponseD D b) (symPath (toApproxCommandRec c x₁ D cB' reflp b com))) rr)
    recResp = λ rr → resp (transportResp rr)
    recRespEx = λ pf rr → respEx pf (transportResp rr)
    φrec = λ rr → φ (transportResp rr)
    φrecEx = λ pf rr → φex pf (transportResp rr)
  in
    descElToGerm D DG rest E b (FC com recResp recRespEx)
    (≤< (smax*-≤-n (FLit 1) ≤⨟ ≤↑ _) lto)
    φrec
    φrecEx
    r

descμToGerm : ∀ {tyCtor} {{æ : Æ}} (E : DCtors ℓ tyCtor) → ( W̃ (λ æ → Arg (λ d → interpDesc {{æ = æ}} (E d) Gtt)) tt)
  → (lto : ∀ d → descSize (E d) <ₛ cSize)
  → (⁇Ty ℓ)
descμBindToGerm : ∀ {tyCtor} {{æ : Æ}} (E : DCtors ℓ tyCtor) → ( LÆ (W̃ (λ æ → Arg (λ d → interpDesc {{æ = æ}} (E d) Gtt)) tt))
  → (lto : ∀ d → descSize (E d) <ₛ cSize)
  → LÆ (⁇Ty ℓ)
descμToGerm E (Wsup (FC (d , com) resp respEx)) lto =
  let
    recFun = descElToGerm (E d) (germCtor ℓ _ d) (dataGermIsCode ℓ _ d) E Gtt (FC com resp respEx) (lto d)
      (λ r → exact {c = C⁇} (descμToGerm {{æ = Approx}} E (resp r) lto))
      λ pf r → descμBindToGerm E (respEx pf r) lto
  in ⁇Tag (⁇μ d (λ r → approx {c = C⁇} (fst (recFun r))) λ pf r → snd (recFun r) pf)
descμToGerm E W℧ lto = ⁇℧
descμToGerm E W⁇ lto = ⁇⁇

--Inlining to help the termination checker
descμBindToGerm E (Now x) lto = pure (descμToGerm E x lto)
descμBindToGerm E (Later x) lto = Later λ tic → descμBindToGerm E (x tic) lto

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
