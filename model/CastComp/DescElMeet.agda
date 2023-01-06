


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
    (⁇Allowed : Bool) {ℓ} (cSize : Size) (vSize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed cSize vSize)

  where

open import Head
open import Util
open import GTypes

open import W

open SmallerCastMeet scm
open import WMuConversion


open import Code

open import CastComp.CastCommandResp ⁇Allowed cSize vSize scm

-- Helper function to take the field-by-field meet for a constructor
descElMeet : ∀ {{æ : Æ}} {cB : ℂ ℓ} {tyCtor : CName} { skel}
      → (D : ℂDesc  cB skel)
      → (E : DCtors ℓ tyCtor)
      → (b1 b2 : ApproxEl cB)
      → (x : ⟦ interpDesc D b1 ⟧F (W̃ (Arg (λ d → interpDesc (E d) Gtt))) tt )
      → (y : ⟦ interpDesc D b2 ⟧F (W̃ (Arg (λ d → interpDesc (E d) Gtt))) tt )
      → (lto : descSize D <ₛ cSize)
      → (ltB : codeSize cB <ₛ cSize)
      → (φ : (r : ResponseD D b1 (toApproxCommandD D b1 (⟦_⟧F.command x)) ) → (r2 : ResponseD D b2 (toApproxCommandD D b2 (⟦_⟧F.command y))) →  (W̃ (Arg (λ d → interpDesc (E d) Gtt)) tt  ))
      → let b12 = cB ∋ b1 ⊓ b2 approxBy Decreasing ltB
        in  LÆ (⟦ interpDesc D b12 ⟧F (W̃ (Arg (λ d → interpDesc (E d) Gtt))) tt)

-- Nothing to do for end case
descElMeet CodeModule.CEnd E b1 b2 (FC tt resp1) (FC tt resp2) lto ltB φ = pure (FC tt (λ ()))
-- For arg, we have to cast the args to the type that's the meet of the types given in the descritptions
-- then take their meet.
descElMeet (CodeModule.CArg c x D cB' reflp) E b1 b2 (FC (a1 , com1) resp1) (FC (a2 , com2) resp2) lto ltB φ = do
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
  -- Transport the response functions based on the above equalites
  let resp1' = λ r → resp1 (transport (cong₂ (ResponseD D) (ΣPathP (reflc , cong fst (sym argEq1))) (cong snd (sym argEq1))) r)
  let resp2' = λ r → resp2 (transport (cong₂ (ResponseD D) (ΣPathP (reflc , cong fst (sym argEq2))) (cong snd (sym argEq2))) r)
  -- Recursively take the meet of the "rest" of the data stored in this inductive type
  (FC com12 resp12) ← descElMeet D E _ _ (FC com1 resp1') (FC com2 resp2')
                      -------------------------------------------
                      (<ₛ-trans (≤ₛ-sucMono (smax*-≤-n (FLit 1))) lto)
                      (<ₛ-trans (≤ₛ-sucMono (smax*-≤-n (FLit 2) )) lto)
                      {!!}
  -- Cast to distribute the meet of the resuting b12 and a12
  -- This should be a no-op, but we can't show that yet
  comRet ← castCommand D _ (b12 , approx a12) com12
                      --------------------------------
                      (<ₛ-trans (≤ₛ-sucMono (smax*-≤-n (FLit 1))) lto)
  -- Same cast for the response function
  respRet ← liftFunDep λ r → do
    r' ← castResponse D _ _ _ _ r
                      ------------------------------------------------
                      (<ₛ-trans (≤ₛ-sucMono (smax*-≤-n (FLit 1))) lto)
    pure (resp12 r')
  -- Package the results up into a member of the right container type
  pure (FC (a12 , comRet) respRet)

descElMeet (CodeModule.CRec c x D cB' reflp) E b1 b2 (FC com1 resp1) (FC com2 resp2) lto ltB φ = do
  let b12 = _ ∋ b1 ⊓ b2
                    -----------------------------
                    approxBy Decreasing ltB
  -- Rest command type is the same as our command type
  -- We need this because the pattern matching is blocked on the approx/exact tag
  let recEq1 = toApproxCommandRec c x D cB' reflp b1 com1
  let recEq2 = toApproxCommandRec c x D cB' reflp b2 com2
  let resp1' = λ r → resp1 (Rest (subst (ResponseD D b1) (sym recEq1) r))
  let resp2' = λ r → resp2 (Rest (subst (ResponseD D b2) (sym recEq2) r))
  -- Compute the meet for all the recursive members of the inductive type stored
  -- We have to use φ as an argument to convince Agda this terminates
  recVals ← liftFunDep λ r → do
    r1 ← ⟨ c b1 ⇐ c b12 ⟩ r
      By Decreasing <ₛ-trans (≤ₛ-sucMono (smax-lub (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)) (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)))) lto
    r2 ← ⟨ c b2 ⇐ c b12 ⟩ r
      By Decreasing <ₛ-trans (≤ₛ-sucMono (smax-lub (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)) (≤ₛ-cocone _ ≤⨟ smax*-≤-n (FLit 0)))) lto
    pure (φ (Rec r1) (Rec r2))
  -- Compute the meet recursively for the rest of the fields
  (FC com12 resp12) ← descElMeet D E b1 b2 (FC com1 resp1') (FC com2 resp2') {!!} ltB {!!}
  -- Same equality issue as above, have to convince it that the command type is the same for the rest
  let req = congPath (ResponseD D b12) (toApproxCommandRec c x D (CΣ _ c) reflp b12 com12)
  -- Package it all back up into a member of the container type
  pure (FC com12 ((λ { (Rec r) → recVals r ; (Rest r) → resp12 (transport req r) }) ))


-- Meets for members of inductive types
descMuMeet : ∀ {{æ : Æ}} {tyCtor : CName}
      → (Ds : DCtors ℓ tyCtor)
      → (x y : W̃ (Arg (λ d → interpDesc (Ds d) Gtt)) tt  )
      → (lto : ∀ {d} → descSize (Ds d) <ₛ cSize)
      → (lto' : S1 <ₛ cSize)
      → LÆ (W̃ (Arg (λ d → interpDesc (Ds d) Gtt)) tt  )
descMuMeet Ds W℧ y lto lto' = pure W℧
descMuMeet Ds x W℧ lto lto' = pure W℧
descMuMeet Ds W⁇ y lto lto' = pure y
descMuMeet Ds x W⁇ lto lto' = pure x
descMuMeet  Ds (Wsup (FC (d , com1) resp1)) (Wsup (FC (d2 , com2) resp2)) lto lto' with decFin d d2
... | no neq = pure W℧
... | yes reflp = do
  -- We need to convince Agda that unit meet with itself is itself
  let 𝟙eq = oMeet𝟙 (self (<cSize lto'))
  -- Compute the helper function that lets us call ourselves recursively in descElMeet
  φ ← liftFunDep λ r1 → liftFunDep λ r2 → descMuMeet Ds (resp1 r1) (resp2 r2) lto lto'
  (FC com𝟙𝟙 resp𝟙𝟙) ← descElMeet (Ds d) Ds Gtt Gtt (FC com1 resp1) (FC com2 resp2)
    lto
    lto'
    φ
  let comRet = substPath (CommandD (Ds d)) 𝟙eq com𝟙𝟙
  let respRet = λ r → resp𝟙𝟙 (transport (cong₂ (ResponseD (Ds d)) (sym 𝟙eq) (congP₂ (λ i x y → toApproxCommandD (Ds d) x y) _ (symP (subst-filler _ _ com𝟙𝟙))) ) r)
  pure (Wsup (FC (d , comRet) respRet ))
