


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
open import Cubical.Foundations.Isomorphism

open import ApproxExact
open import InductiveCodes
open import CodeSize
-- open import CodePair
open import WMuEq
open import SizeOrd
open import Assumption

open import CastComp.Interface

module CastComp.DataGermMeet {{dt : DataTypes}} {{dg : DataGerms}} {{ic : InductiveCodes}}
    (⁇Allowed : ⁇Flag){ℓ} (cSize : Size) (vSize : Size) (scm : SmallerCastMeet ⁇Allowed ℓ cSize vSize)

  where

open import Code
open import Head
open import Util
open import WellFounded


open SmallerCastMeet scm




  -- → (W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ)) (⁇Ty ℓ) tt)

germFIndMeet : ∀ {{æ : Æ}} {B+ B- sig} {tyCtor : CName}
  → {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p cSize}
  → {@(tactic assumption) cpf : if¬Pos ⁇Allowed (S1 ≡p cSize)  (SZ ≡p cSize)}
  → (D : GermCtor B+ B- sig)
  → (isCode : DataGermIsCode ℓ D)
  → (b+ : B+)
  → (b- : B- b+)
  → (cs1 cs2 : FCGerm ℓ tyCtor D b+ b-)
  → (smax (germFCSize isCode cs1) (germFCSize isCode cs2) <ₛ vSize)
  → LÆ (FContainer (interpGermCtor' D b+ b- ) (W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ)) (⁇Ty ℓ) tt)
germFIndMeet GEnd GEndCode b+ b- cs1 cs2 lt = pure (FC tt (λ ()) λ ())
-- We've got two parts, the recursive value and the "rest"
-- Take the meet of both recursively then put them back together
germFIndMeet {tyCtor = tyCtor} {cpf = cpf} (GRec D) (GRecCode isCode) b+ b- (FC c1 r1 u1) (FC c2 r2 u2) lt
  = do
    (FC crec rrec urec) ← germFIndMeet D isCode  b+ b- (FC c1 (λ r → r1 (Rest r)) u1) (FC c2 (λ r → r2 (Rest r)) u2)
      (<ₛ-trans (smax-strictMono (≤ₛ-sucMono smax-≤R) (≤ₛ-sucMono smax-≤R)) lt)
    let lt' = (≤< (smax-mono (<-in-≤ (≤ₛ-sucMono smax-≤L)) (<-in-≤ (≤ₛ-sucMono smax-≤L))) lt)
    xrec ← oDataGermMeet (self (<VSize reflc lt'))
      (r1 (Rec tt)) (r2 (Rec tt)) reflp
    pure (FC crec (λ { (Rec x) → xrec ; (Rest x) → rrec x}) urec)
germFIndMeet (GHRec A D) (GHRecCode c+ c- iso+ iso- isCode) b+ b- (FC c1 r1 u1) (FC c2 r2 u2) lt = do
    (FC crec rrec urec) ← germFIndMeet D isCode  b+ b- (FC c1 (λ r → r1 (Rest {!!})) u1) (FC c2 (λ r → r2 (Rest {!!})) u2)
      {!!}
    xrec ← liftFun λ a → do
      let lt' = ≤< (smax-mono (<-in-≤ (≤ₛ-sucMono ({!!} ≤⨟ ≤ₛ-cocone {!Iso.fun (iso- b-)!} ≤⨟ ≤ₛ-cocone (Iso.fun (iso+ b+) (fst a))))) {!!}) lt
      oDataGermMeet (self (<VSize reflc lt'))
        (r1 (Rec a)) (r2 (Rec a)) reflp
    pure (FC crec (λ { (Rec x) → xrec x ; (Rest (a , resp)) → rrec resp}) urec)
germFIndMeet (GUnk A D) (GUnkCode c+ c- iso+ iso- isCode)  b+ b- cs1 cs2 lt = {!!}
germFIndMeet (GArg (A+ , A-) D) (GArgCode c+ c- iso+ iso- isCode)  b+ b-
  (FC ((a+1 , a-1) , c1) r1 u1) (FC ((a+2 , a-2) , c2) r2 u2) lt = do
  a+ ← c+ b+ ∋ Iso.fun (iso+ b+) a+1 ⊓ Iso.fun (iso+ b+) a+2
    cBy {!!}
    vBy {!!}
  xrec ← germFIndMeet D isCode (b+ , Iso.inv (iso+ b+) a+) {!!} (FC {!c1!} {!!} {!!}) {!!} {!!}
  pure {!!}



germIndMeet : ∀ {{æ : Æ}} {tyCtor}
  →  {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p cSize}
  → {@(tactic assumption) cpf : if¬Pos ⁇Allowed (S1 ≡p cSize)  (SZ ≡p cSize)}
  → (x y : DataGerm ℓ tyCtor)
  →  smax (germIndSize tyCtor x) (germIndSize tyCtor y) <ₛ vSize
  → LÆ (DataGerm ℓ tyCtor)
germIndMeet W℧ y eq = pure W℧
germIndMeet W⁇ y eq =  pure y
germIndMeet x W℧ eq = pure W℧
germIndMeet x W⁇ eq = pure x
germIndMeet {tyCtor} {posNoCode = posNoCode} {cpf} (Wsup x) (Wsup y) lt
  with (d , x' , xlt) ← germMatch x
  with (dy , y' , ylt) ← germMatch y
  with decFin d dy
... | yes reflp = do
  fcRet ← germFIndMeet {posNoCode = posNoCode} {cpf} (germForCtor ℓ tyCtor d) (dataGermIsCode ℓ tyCtor d) tt tt x' y'
    (<ₛ-trans (smax-strictMono xlt ylt) lt)
  pure (dataGermInj fcRet)
-- Meet is error if they have different data constructors
... | no npf = pure W℧
  -- ... | no npf = ?
-- germIndMeet {tyCtor = tyCtor} x y eq = wInd {!!} {!!} {!!} {!!} x
