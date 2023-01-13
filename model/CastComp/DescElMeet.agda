


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

module CastComp.DescElMeet {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ} (cSize : Size)  (scm : SmallerCastMeet ℓ ⁇Allowed cSize )

  where

open import Head
open import Util
open import GTypes

open import W

open SmallerCastMeet scm
open import WMuConversion


open import Code

open import CastComp.CastCommandResp ⁇Allowed cSize scm

-- Helper function to take the field-by-field meet for a constructor
descElMeet : ∀ {{æ : Æ}} {cB : ℂ ℓ} {tyCtor : CName} { skel}
      → (D : ℂDesc  cB skel)
      → (E : DCtors ℓ tyCtor)
      → (b1 b2 : ApproxEl cB)
      → (x : ⟦ interpDesc D b1 ⟧F  (λ æ → W̃ {{æ = æ}} (λ æ → Arg (λ d → interpDesc {{æ = æ}} (E d) Gtt))) tt )
      → (y : ⟦ interpDesc D b2 ⟧F  (λ æ → W̃ {{æ = æ}} (λ æ → Arg (λ d → interpDesc {{æ = æ}} (E d) Gtt))) tt )
      → (lto : descSize D <ₛ cSize)
      → (ltB : codeSize cB <ₛ cSize)
      → (φ : (r : ResponseD D b1 (toApproxCommandD D b1 (⟦_⟧F.command x)) ) → (r2 : ResponseD D b2 (toApproxCommandD D b2 (⟦_⟧F.command y))) →  (W̃ {{æ = Approx}} (λ æ → Arg (λ d → interpDesc {{æ = æ}} (E d) Gtt)) tt  ))
      → (φEx : (IsExact æ) → (r : ResponseD D b1 (toApproxCommandD D b1 (⟦_⟧F.command x)) ) → (r2 : ResponseD D b2 (toApproxCommandD D b2 (⟦_⟧F.command y))) → LÆ (W̃ {{æ = æ}} (λ æ → Arg (λ d → interpDesc {{æ = æ}} (E d) Gtt)) tt  ))
      → let b12 = cB ∋ b1 ⊓ b2 approxBy Decreasing ltB
        in  LÆ (⟦ interpDesc D b12 ⟧F (λ æ → W̃ {{æ = æ }} (λ æ → Arg (λ d → interpDesc {{æ = æ}} (E d) Gtt)))  tt)

-- Nothing to do for end case
descElMeet CodeModule.CEnd E b1 b2 (FC tt resp1 exact1) (FC tt resp2 exact2) lto ltB φ φEx = pure (FC tt (λ ()) λ _ ())
-- For arg, we have to cast the args to the type that's the meet of the types given in the descritptions
-- then take their meet.
descElMeet (CodeModule.CArg c x D cB' reflp) E b1 b2 (FC (a1 , com1) resp1 exact1) (FC (a2 , com2) resp2 exact2) lto ltB φ φEx = do
  let b12 = _ ∋ b1 ⊓ b2
                     ---------------------------------------------
                     approxBy Decreasing ltB
  a1-12 ← ⟨ c b12 ⇐ c b1 ⟩ a1
                    ----------------------------------------------
                    By Decreasing
                      <ₛ-trans
                        (≤ₛ-sucMono (smax-lub (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)) (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0))))
                        lto
  a2-12 ← ⟨ c b12 ⇐ c b2 ⟩ a2
                    ---------------------------------------------
                    By Decreasing
                      <ₛ-trans
                        (≤ₛ-sucMono (smax-lub (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)) (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0))))
                        lto
  a12 ← c b12 ∋ a1-12 ⊓ a2-12
                    --------------------------------------------
                    By Decreasing
                      <ₛ-trans
                        (≤ₛ-sucMono (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)))
                        lto
  -- Lemmas that let us take fst and snd of the approx of the pair that makes up the new command for the rest of the data
  -- We need this because the pattern matching is blocked on the approx/exact tag
  let argEq1 = toApproxCommandArg c x D cB' reflp b1 a1 com1
  let argEq2 = toApproxCommandArg c x D cB' reflp b2 a2 com2
  let req1 = (cong₂ (ResponseD D) (ΣPathP (reflc , cong fst (sym argEq1))) (cong snd (sym argEq1)))
  let req2 = (cong₂ (ResponseD D) (ΣPathP (reflc , cong fst (sym argEq2))) (cong snd (sym argEq2)))
  -- Transport the response functions based on the above equalites
  let resp1' = λ r → resp1 (transport req1 r)
  let resp2' = λ r → resp2 (transport req2 r)
  let exact1' = λ pf r → exact1 pf (transport req1 r)
  let exact2' = λ pf r → exact2 pf (transport req2 r)
  -- Recursively take the meet of the "rest" of the data stored in this inductive type
  (FC com12 resp12 exact12) ← descElMeet D E _ _ (FC com1 resp1' exact1') (FC com2 resp2' exact2')
                      -------------------------------------------
                      (<ₛ-trans (≤ₛ-sucMono (smax*-≤-n (FLit 1))) lto)
                      (<ₛ-trans (≤ₛ-sucMono (smax*-≤-n (FLit 2) )) lto)
                      (λ r1 r2 → φ (transport req1 r1) (transport req2 r2))
                      λ pf r1 r2 → φEx pf (transport req1 r1) (transport req2 r2)
  -- Cast to distribute the meet of the resuting b12 and a12
  -- This should be a no-op, but we can't show that yet
  comRet ← castCommand D _ (b12 , approx a12) com12
                      --------------------------------
                      (<ₛ-trans (≤ₛ-sucMono (smax*-≤-n (FLit 1))) lto)
  -- Same cast for the response function
  let
    respRet =
      λ r →
        let
          ra = toApproxResponseD D _ _ r
          r' = castResponse {{æ = Approx}} D _ _ _ _ ra
                      ------------------------------------------------
                      (<ₛ-trans (≤ₛ-sucMono (smax*-≤-n (FLit 1))) lto)
        in resp12 (toÆResponseD _ _ _ (fromL r'))
  let exactRet = λ pf r → do
    r' ← castResponse D _ _ _ _ r 
                      ------------------------------------------------
                      (<ₛ-trans (≤ₛ-sucMono (smax*-≤-n (FLit 1))) lto)
    exact12 pf r'
  -- fromL do
  --   r' ← castResponse {{æ = Approx }} D _ _ _ _ ?
  --   pure {{æ = Approx}} (resp12 r')
  -- Package the results up into a member of the right container type
  pure (FC (a12 , comRet) respRet exactRet)

descElMeet {{æ = æ}} (CodeModule.CRec cdom x D cB' reflp) E b1 b2 (FC com1 resp1 exact1) (FC com2 resp2 exact2) lto ltB φ φEx = do
  let b12 = _ ∋ b1 ⊓ b2
                    -----------------------------
                    approxBy Decreasing ltB
  -- Rest command type is the same as our command type
  -- We need this because the pattern matching is blocked on the approx/exact tag
  let recEq1 = toApproxCommandRec cdom x D cB' reflp b1 com1
  let recEq2 = toApproxCommandRec cdom x D cB' reflp b2 com2
  let resp1' = λ r → resp1 (Rest (subst (ResponseD D b1) (sym recEq1) r))
  let resp2' = λ r → resp2 (Rest (subst (ResponseD D b2) (sym recEq2) r))
  let exact1' = λ pf r → exact1 pf (Rest (subst (ResponseD D b1) (sym recEq1) r))
  let exact2' = λ pf r → exact2 pf (Rest (subst (ResponseD D b2) (sym recEq2) r))
  -- Compute the meet for all the recursive members of the inductive type stored
  -- We have to use φ as an argument to convince Agda this terminates
  -- Compute the meet recursively for the rest of the fields
  (FC com12 resp12 exact12) ← descElMeet D E b1 b2 (FC com1 resp1' exact1') (FC com2 resp2' exact2')
    (<ₛ-trans (≤ₛ-sucMono (smax*-≤-n (FLit 1))) lto)
    ltB
    ( λ r1 r2 → φ (Rest (transport (congPath (ResponseD D b1) (sym recEq1)) r1)) (Rest (transport (congPath (ResponseD D b2) (sym recEq2)) r2)) )
    ( λ pf r1 r2 → φEx pf (Rest (transport (congPath (ResponseD D b1) (sym recEq1)) r1)) (Rest (transport (congPath (ResponseD D b2) (sym recEq2)) r2)) )
  let
    recVals : (r : El (cdom b12) ) → _
    recVals =
      λ r →
        let
          r1 = ⟨ cdom b1 ⇐ cdom b12 ⟩ (approx r)
                 approxBy Decreasing <ₛ-trans (≤ₛ-sucMono (smax-lub (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)) (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)))) lto
          r2 = ⟨ cdom b2 ⇐ cdom b12 ⟩ (approx r)
                 approxBy Decreasing <ₛ-trans (≤ₛ-sucMono (smax-lub (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)) (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)))) lto
        in (φ (Rec (exact r1)) (Rec (exact r2)))
    exactRecVals : (IsExact æ) → (r : El (cdom b12) ) → _
    exactRecVals pf r = do
        r1 ← [ æ ]⟨ cdom b1 ⇐ cdom b12 ⟩ r
                 By Decreasing <ₛ-trans (≤ₛ-sucMono (smax-lub (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)) (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)))) lto
        r2 ← [ æ ]⟨ cdom b2 ⇐ cdom b12 ⟩ r
                 By Decreasing <ₛ-trans (≤ₛ-sucMono (smax-lub (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)) (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)))) lto
        (φEx pf (Rec r1) (Rec r2))
  -- Same equality issue as above, have to convince it that the command type is the same for the rest
  let req = congPath (ResponseD D b12) (toApproxCommandRec cdom x D _ reflp b12 com12)
  -- Package it all back up into a member of the container type
  pure (FC
    com12
    ((λ { (Rec r) → recVals r ; (Rest r) → resp12 (transport req r) }) )
    (λ pf → λ {(Rec r) → exactRecVals pf r ; (Rest r) → exact12 pf (transport req r)}))


-- Meets for members of inductive types
descMuMeet : ∀ {{æ : Æ}} {tyCtor : CName}
      → (Ds : DCtors ℓ tyCtor)
      → (x y : W̃ (λ æ → Arg (λ d → interpDesc {{æ = æ}} (Ds d) Gtt)) tt  )
      → (lto : ∀ {d} → descSize (Ds d) <ₛ cSize)
      → (lto' : S1 <ₛ cSize)
      → LÆ (W̃ (λ æ → Arg (λ d → interpDesc {{æ = æ}} (Ds d) Gtt)) tt  )
descMuBindMeet : ∀ {{æ : Æ}} {tyCtor : CName}
      → (Ds : DCtors ℓ tyCtor)
      → (x y : LÆ (W̃ (λ æ → Arg (λ d → interpDesc {{æ = æ}} (Ds d) Gtt)) tt)  )
      → (lto : ∀ {d} → descSize (Ds d) <ₛ cSize)
      → (lto' : S1 <ₛ cSize)
      → LÆ (W̃ (λ æ → Arg (λ d → interpDesc {{æ = æ}} (Ds d) Gtt)) tt  )

descMuMeet Ds W℧ y lto lto' = pure W℧
descMuMeet Ds x W℧ lto lto' = pure W℧
descMuMeet Ds W⁇ y lto lto' = pure y
descMuMeet Ds x W⁇ lto lto' = pure x
descMuMeet {{æ = æ}} Ds (Wsup (FC (d , com1) resp1 exact1)) (Wsup (FC (d2 , com2) resp2 exact2)) lto lto' with decFin d d2
... | no neq = pure W℧
... | yes reflp = do
  -- We need to convince Agda that unit meet with itself is itself
  let 𝟙eq = oMeet𝟙 (self (<cSize lto'))
  -- Compute the helper function that lets us call ourselves recursively in descElMeet
  let φ = λ r1 r2 → fromL (descMuMeet ⦃ æ = Approx ⦄ Ds (resp1 r1) (resp2 r2) lto lto')
  let φEx = λ pf r1 r2 → descMuBindMeet Ds (exact1 pf r1) (exact2 pf r2) lto lto'

  -- λ r1 r2 → descMuMeet Ds (resp1 r1) (resp2 r2) lto lto'
  (FC com𝟙𝟙 resp𝟙𝟙 exact𝟙𝟙) ← descElMeet (Ds d) Ds Gtt Gtt (FC com1 resp1 exact1) (FC com2 resp2 exact2)
    lto
    lto'
    φ
    φEx
  let comRet = substPath (CommandD (Ds d)) 𝟙eq com𝟙𝟙
  let respRet = λ r → resp𝟙𝟙 (transport (cong₂ (ResponseD (Ds d)) (sym 𝟙eq) (congP₂ (λ i x y → toApproxCommandD (Ds d) x y) _ (symP (subst-filler _ _ com𝟙𝟙))) ) r)
  let exactRet = λ pf r → exact𝟙𝟙 pf (transport (cong₂ (ResponseD (Ds d)) (sym 𝟙eq) (congP₂ (λ i x y → toApproxCommandD (Ds d) x y) _ (symP (subst-filler _ _ com𝟙𝟙))) ) r)
  pure (Wsup (FC (d , comRet) respRet exactRet ))

descMuBindMeet Ds (Later x) y lto lto' = Later λ tic → descMuBindMeet Ds (x tic) y lto lto'
descMuBindMeet Ds x (Later y)  lto lto' = Later λ tic → descMuBindMeet Ds x (y tic) lto lto'
descMuBindMeet Ds (Now x) (Now y)  lto lto' = descMuMeet Ds x y lto lto'
