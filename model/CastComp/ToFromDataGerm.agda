


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



-- Same as above, but going from the germ instead of to
descElFromGerm : ∀ {{æ : Æ}} {cB : ℂ ℓ} {tyCtor : CName} { skel}
      → (D : ℂDesc  cB skel)
      → (DG : GermCtor skel)
      → (isCode : GermCtorIsCode ℓ DG)
      → (E : DCtors ℓ tyCtor)
      → (b : ApproxEl cB)
      → (xAppr : (r : GermResponse DG) → ⁇Ty ℓ)
      → (xExact : IsExact æ → (r : GermResponse DG) → LÆ (⁇Ty ℓ))
      → (lto : descSize D <ₛ cSize)
      → (φ : (r : GermResponse DG) → ( W̃ (λ æ → Arg (λ d → interpDesc {{æ = æ}} (E d) Gtt)) tt) )
      → (φex : IsExact æ → (r : GermResponse DG) → LÆ ( W̃ (λ æ → Arg (λ d → interpDesc {{æ = æ}} (E d) Gtt)) tt) )
      → (⟦ interpDesc D b ⟧F  (λ æ → W̃ {{æ = æ}} (λ æ → Arg (λ d → interpDesc {{æ = æ}} (E d) Gtt))) tt )
descElFromGerm CodeModule.CEnd GEnd GEndCode E b resp respEx lto φ φex = FC tt (λ ()) (λ _ ())
descElFromGerm (CodeModule.CArg c ar D cB' reflp) (GArg A DG) (GArgCode cr cIso isCode) E b resp respEx lto φ φex = let
    --Calculate a new argument function by casting its arguments to the germ resposne type for the argument,
    --then casting the result back from ⁇
    aFun = λ x → let
      rCast = decRec
        (λ pf → fromL (oCast (selfGermNeg (ptoc pf)) {{æ = Approx}} (HasArity.arDom (ar b)) cr (approx x) reflp) )
        (λ _ → ℧Approx cr)
        (⁇Allowed ≟ true)
      rGerm = Iso.inv cIso (exact rCast)
      approxRet = ⟨ HasArity.arCod (ar b) (approx x) ⇐ C⁇ ⟩ (approx {c = C⁇} (resp (inl rGerm)))
        approxBy  Decreasing ≤< (codeMaxL _ ≤⨟ <-in-≤ (arityCod≤ (ar b)) ≤⨟ ≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0) ≤⨟ ≤↑ _) lto
      --Same thing but in exact mode
      exComp = λ pf → do
        rCastEx ← decRec
          (λ pf →  (oCast (selfGermNeg (ptoc pf)) (HasArity.arDom (ar b)) cr x reflp) )
          (λ _ → pure (℧ cr))
          (⁇Allowed ≟ true)
        let rGermEx = Iso.inv cIso rCastEx
        funResult ← respEx pf (inl rGermEx)
        ⟨ HasArity.arCod (ar b) (approx x) ⇐ C⁇ ⟩ funResult
          By Decreasing ≤< (codeMaxL _ ≤⨟ <-in-≤ (arityCod≤ (ar b)) ≤⨟ ≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0) ≤⨟ ≤↑ _) lto
      in (exact approxRet) , exComp
    -- Transport the function to our code type with the stored equality in the arity
    aRet = transport⁻ (congPath (λ c → ÆEl c _) (HasArity.arEq (ar b))) aFun
    -- Recursively cast the rest of the fields
    (FC com retAppr retEx) = descElFromGerm D DG isCode E _
      (λ r → resp (inr r))
      (λ pf r → respEx pf (inr r))
      (≤< (smax*-≤-n (FLit 1) ≤⨟ ≤↑ _) lto)
      (λ r → φ (inr r))
      λ pf r → φex pf (inr r)
  in
    FC
      (aRet , com)
      (λ r → retAppr (subst (λ x → ResponseD D (b , fst x) (snd x)) (toApproxCommandArg c ar D cB' reflp _ _ _ ) r))
      (λ pf r → retEx pf (subst (λ x → ResponseD D (b , fst x) (snd x)) (toApproxCommandArg c ar D cB' reflp _ _ _ ) r))
descElFromGerm (CodeModule.CRec c x D cB' reflp) (GRec A DG) (GRecCode cr cIso isCode) E b resp respEx lto φ φex  = let
  -- The function returning the datatype itself
  indGetterFun : (r : _) → _
  indGetterFun = λ x → let
      rCast = decRec
        (λ pf → fromL (oCast (selfGermNeg (ptoc pf)) {{æ = Approx}} (c b) cr (approx x) reflp) )
        (λ _ → ℧Approx cr)
        (⁇Allowed ≟ true)
    in approxμ _ _ _ _ (φ (inl (Iso.inv cIso (exact rCast))))
  indGetterFunEx : (IsExact _) → (r : _) → _
  indGetterFunEx = λ pf x → do
      rCastEx ← decRec
        (λ pf → (oCast (selfGermNeg (ptoc pf)) (c b) cr x reflp) )
        (λ _ → pure (℧ cr))
        (⁇Allowed ≟ true)
      φex pf (inl (Iso.inv cIso rCastEx))

  (FC com retAppr retEx) = descElFromGerm D DG isCode E _
      (λ r → resp (inr r))
      (λ pf r → respEx pf (inr r))
      (≤< (smax*-≤-n (FLit 1) ≤⨟ ≤↑ _) lto)
      (λ r → φ (inr r))
      (λ pf r → φex pf (inr r))
  in
    FC
      com
      (λ {(Rec r) → indGetterFun r ; (Rest r) → retAppr (subst (ResponseD D b) (toApproxCommandRec c x D cB' reflp _ _ ) r)})
      (λ pf → λ {(Rec r) → indGetterFunEx pf r ; (Rest r) → retEx pf (subst (ResponseD D b) (toApproxCommandRec c x D cB' reflp _ _ ) r)})


descμFromGerm : ∀ {tyCtor} {{æ : Æ}} (E : DCtors ℓ tyCtor) →  ⁇Ty ℓ
  → (lto : ∀ d → descSize (E d) <ₛ cSize)
  → ( W̃ (λ æ → Arg (λ d → interpDesc {{æ = æ}} (E d) Gtt)) tt)
descμBindFromGerm : ∀ {tyCtor} {{æ : Æ}} (E : DCtors ℓ tyCtor) → LÆ (⁇Ty ℓ)
  → (lto : ∀ d → descSize (E d) <ₛ cSize)
  → LÆ ( W̃ (λ æ → Arg (λ d → interpDesc {{æ = æ}} (E d) Gtt)) tt)

-- Take an element of ⁇ and check if it's an embedded member of the right inductive type
-- If it is, traverse it to convert all its fields
-- otherwise, error
descμFromGerm {tyCtor = tyCtor} E (⁇Tag {h = HCtor tyCtor'} (⁇μ d resp respEx)) lto with decFin tyCtor tyCtor'
... | no _ = W℧
... | yes reflp = let
    (FC com retResp retEx) = descElFromGerm (E d) (germCtor ℓ _ d) (dataGermIsCode ℓ _ d) E Gtt
      (λ r → exact {c = C⁇} (resp r))
      (λ r → (respEx r))
      (lto d)
      (λ r → exactμ tyCtor C𝟙 E Gtt (descμFromGerm {{æ = Approx}} E (resp r) lto))
      (λ pf r → descμBindFromGerm  E (respEx pf r) lto)
  in Wsup (FC (d , com) retResp retEx)
-- ⁇ At the unknown type becomes ⁇ in the inductive type
descμFromGerm E ⁇⁇ lto = W⁇
descμFromGerm E _ lto = W℧

--Inlining to help the termination checker
descμBindFromGerm E (Now x) lto = pure (descμFromGerm E x lto)
descμBindFromGerm E (Later x) lto = Later λ tic → descμBindFromGerm E (x tic) lto
