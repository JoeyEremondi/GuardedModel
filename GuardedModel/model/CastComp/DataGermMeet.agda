


-- Bound on the size of the meet on codes, assuming we have meet, cast, etc. for smaller types


open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sum as Sum
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
    (⁇Allowed : ⁇Flag){ℓ} (size : Size)  (scm : SmallerCastMeet ⁇Allowed ℓ size)

  where

open import Code
open import Head
open import Util
open import WellFounded


open SmallerCastMeet scm



commandSize : ∀ {{æ : Æ}} {B+ : Set}  {B- : B+ → Set} { sig} (tyCtor : CName)
  → (D : GermCtor B+ B- sig)
  → (isCode : DataGermIsCode ℓ D)
  → (b+ : B+)
  → (b- : B- b+)
  → Command
      (interpGermCtor' D b+ b-)
      (just tyCtor)
  → Size
commandSize tyCtor (GArg (A+ , _) D) (GArgCode c+ c- iso+ iso- isCode) b+ b- ((a+ , a-) , rest) = S↑ (smax (elSize (c+ b+) (Iso.fun (iso+ b+) a+)) (commandSize tyCtor D isCode (b+ , a+) (b- , a-)  rest))
commandSize tyCtor GEnd GEndCode b+ b- x = S1
commandSize tyCtor (GHRec A D) (GHRecCode c+ c- iso+ iso- isCode) b+ b- x = commandSize tyCtor D isCode b+ b- x
commandSize tyCtor (GRec D) (GRecCode isCode) b+ b- x = commandSize tyCtor D isCode b+ b- x
commandSize tyCtor (GUnk A D) (GUnkCode c+ c- iso+ iso- isCode) b+ b- x = commandSize tyCtor D isCode b+ b- x

castCommand : ∀ {{æ : Æ}} {B+ : Set}  {B- : B+ → Set} { sig} {tyCtor : CName}
  → {@(tactic assumption) pos : ⁇Allowed ≡p ⁇pos }
  → (D : GermCtor B+ B- sig)
  → (isCode : DataGermIsCode ℓ D)
  → (b+1 : B+)
  → (b-1 : B- b+1)
  → (b+2 : B+)
  → (b-2 : B- b+2)
  → (x : Command
      (interpGermCtor' D b+1 b-1)
      (just tyCtor))
  → commandSize tyCtor D isCode b+1 b-1 x <ₛ size
  → LÆ ( Command
      (interpGermCtor' D b+2 b-2)
      (just tyCtor) )
castCommand (GArg (A+ , A-) D) (GArgCode c+ c- iso+ iso- isCode) b+1 b-1 b+2 b-2 ((a+1 , a-1) , x) lt = do
  ca+2 ← ⟨ c+ b+2 ⇐ c+ b+1 ⟩ Iso.fun (iso+ b+1) a+1 By argPos (≤< (≤suc smax-≤L) lt)
  let a+2 = Iso.inv (iso+ b+2) ca+2
  let
    ma-2 : LÆ (A- b+2 (Iso.inv (iso+ b+2) ca+2) b-2)
    ma-2 = caseÆ
      (λ eq → pure (Iso.inv (iso- b+2 (Iso.inv (iso+ b+2) ca+2) b-2) (▹Default eq)))
      λ eq → do
        ca-1 ← θ eq (Iso.fun (iso- b+1 a+1 b-1) a-1)
        gSelf ← Lself {al = ⁇pos} eq
        (ca-2 , _) ← oCast gSelf (c- b+1 a+1 b-1) (c- b+2 a+2 b-2) ca-1 reflp
        pure (Iso.inv (iso- b+2 (Iso.inv (iso+ b+2) ca+2) b-2) (next ca-2))
  a-2 ← ma-2
    -- Iso.inv (iso- b+2 (Iso.inv (iso+ b+2) ca+2) b-2) (next ca-2)
  crest ← castCommand D isCode (b+1 , a+1) (b-1 , a-1) (b+2 , a+2) (b-2 , a-2) x (≤< (≤suc smax-≤R) lt)
  pure ((a+2 , a-2) , crest)
castCommand GEnd GEndCode b+1 b-1 b+2 b-2 lt x = pure tt
castCommand (GHRec A D) (GHRecCode c+ c- iso+ iso- isCode) b+1 b-1 b+2 b-2 x lt = castCommand D isCode b+1 b-1 b+2 b-2 x lt
castCommand (GRec D) (GRecCode isCode) b+1 b-1 b+2 b-2 x lt = castCommand D isCode b+1 b-1 b+2 b-2 x lt
castCommand (GUnk A D) (GUnkCode c+ c- iso+ iso- isCode) b+1 b-1 b+2 b-2 x lt = castCommand D isCode b+1 b-1 b+2 b-2 x lt


commandSizeLt : ∀ {{æ : Æ}} {B+ B- sig} (tyCtor : CName)
  → {@(tactic assumption) isPos : ⁇Allowed ≡p ⁇pos }
  → (D : GermCtor B+ B- sig)
  → (isCode : DataGermIsCode ℓ D)
  → (b+ : B+)
  → (b- : B- b+)
  → ((FC com resp) : DescFunctor ℓ tyCtor D b+ b-)
  → commandSize tyCtor D isCode b+ b- com ≤ₛ germIndSize tyCtor D isCode b+ b- (FC com resp)
commandSizeLt tyCtor GEnd GEndCode b+ b- (FC com resp) = ≤ₛ-refl
commandSizeLt tyCtor (GArg (A+ , A-) D) (GArgCode c+ c- iso+ iso- isCode) b+ b- (FC com resp)
  = ≤ₛ-sucMono ?
commandSizeLt tyCtor (GHRec A D) (GHRecCode c+ c- iso+ iso- isCode) b+ b- (FC com resp) =
  commandSizeLt tyCtor D isCode b+ b- _ ≤⨟ ≤suc ( smax*-≤-n (Fin.suc (Fin.suc Fin.zero)) ≤⨟ ≤ₛ-cocone (℧Approxed (c+ b+)))
commandSizeLt tyCtor (GRec D) (GRecCode isCode) b+ b- (FC com resp)
  = commandSizeLt tyCtor D isCode b+ b- _ ≤⨟ ≤suc smax-≤R
commandSizeLt tyCtor (GUnk A D) (GUnkCode c+ c- iso+ iso- isCode) b+ b- (FC com resp)
  = commandSizeLt tyCtor D isCode b+ b- _ ≤⨟ ≤suc (smax*-≤-n (Fin.suc (Fin.suc Fin.zero)) ≤⨟ ≤ₛ-cocone (℧Approxed (c+ b+)))

germFIndMeet : ∀ {{æ : Æ}} {B+ B- sig} {tyCtor : CName}
  → {@(tactic assumption) isPos : ⁇Allowed ≡p ⁇pos }
  → (D : GermCtor B+ B- sig)
  → (isCode : DataGermIsCode ℓ D)
  → (b+ : B+)
  → (b- : B- b+)
  → (cs1 cs2 : DescFunctor ℓ tyCtor D b+ b-)
  → (smax (germIndSize tyCtor D isCode b+ b- cs1) (germIndSize tyCtor D isCode b+ b- cs2) <ₛ size)
  → LÆ (DescFunctor ℓ tyCtor D b+ b-)
germFIndMeet GEnd GEndCode b+ b- cs1 cs2 lt = pure (FC tt λ {(inl ()) ; (inr ())})
-- We've got two parts, the recursive value and the "rest"
-- Take the meet of both recursively then put them back together
germFIndMeet {{æ = æ}} {tyCtor = tyCtor} (GRec D) (GRecCode isCode) b+ b- (FC c1 r1) (FC c2 r2) lt
  = do
    let lt' = ≤< (smax-mono (≤↑ _ ≤⨟ ≤ₛ-sucMono smax-≤L) (≤↑ _ ≤⨟ ≤ₛ-sucMono smax-≤L)) lt
    -- Get the two elements of the datatype stored
    let x1 = r1 (inl (Rec tt))
    let x2 = r2 (inl (Rec tt))
    -- Take the meet of the two recursive elements
    xrec ← oDataGermMeet (self (<Size  lt')) x1 x2 reflp
    -- Take the meet of whatever else is stored in the datatype
    (FC crec rrec ) ← germFIndMeet D isCode  b+ b-
      (FC c1 (Sum.elim
        (λ r → r1 (inl (Rest r)))
        (λ r → r1 (inr r) )))
      (FC c2 (Sum.elim
        (λ r → r2 (inl (Rest r)))
        (λ r → r2 (inr r) )))
      (<ₛ-trans (smax-strictMono (≤ₛ-sucMono smax-≤R) (≤ₛ-sucMono smax-≤R)) lt)
    pure (FC crec (λ { (inl (Rec tt)) → xrec ; (inl (Rest x)) → rrec (inl x)}) )
-- germFIndMeet {{æ = æ}} {tyCtor = tyCtor} {posNoCode = pnc} {cpf = cpf} (GHRec (A+ , A-) D) (GHRecCode c+ c- iso+ iso- isCode) b+ b- (FC c1 r1 u1) (FC c2 r2 u2) lt = do
--     (FC crec rrec urec) ← germFIndMeet  D isCode  b+ b- (FC c1 (λ r → r1 (Rest r)) u1) (FC c2 (λ r → r2 (Rest r)) u2)
--       {!!}
--     -- New function computes the meet of the old functions
--     f+ ← liftFun λ (a+ : A+ b+) → do
--       let lt' = {!!}
--       oDataGermMeet (self (<Size  lt')) {posNoCode = pnc} {cpf = cpf} (r1 (Rec (inl a+))) (r2 (Rec (inl a+))) reflp
--     let
--       lf- : LÆ (Σ[ a+ ∈ A+ b+ ](A- b+ a+ b-) → DataGerm ℓ tyCtor)
--       lf- = liftFun λ {(a+ , a-) → caseÆ
--         -- Approx case
--         (λ {reflp → do
--           let
--             lt' = ≤< (smax-mono
--               -- Left side
--               (≤↑ _ ≤⨟ ≤ₛ-sucMono ( smax*-≤-n (Fin.suc Fin.zero)
--               ≤⨟ smax*-monoR (smax*-monoL
--               (subst (λ x → germIndSize ⦃ æ = Approx ⦄ tyCtor (r1 (Rec (inr x))) ≤ₛ _)
--                       (ΣnegUnique ⦃ æ = Approx ⦄ {X = λ a → ApproxEl (c- b+ a b-)} reflp (iso- b+ _ b-) (Iso.inv (iso+ b+) (Iso.fun (iso+ b+) a+) , Iso.inv (iso- b+ _ b-) tt*) (a+ , a-) (Iso.leftInv (iso+ b+) a+)) ≤ₛ-refl)
--                       )
--               ≤⨟  ≤ₛ-cocone {{æ = Approx}} (Iso.fun (iso+ b+) a+) ))
--               --right side
--               (≤↑ _ ≤⨟ ≤ₛ-sucMono ( smax*-≤-n (Fin.suc Fin.zero)
--               ≤⨟ smax*-monoR (smax*-monoL
--               (subst (λ x → germIndSize ⦃ æ = Approx ⦄ tyCtor (r2 (Rec (inr x))) ≤ₛ _)
--                       (ΣnegUnique ⦃ æ = Approx ⦄ {X = λ a → ApproxEl (c- b+ a b-)} reflp (iso- b+ _ b-) (Iso.inv (iso+ b+) (Iso.fun (iso+ b+) a+) , Iso.inv (iso- b+ _ b-) tt*) (a+ , a-) (Iso.leftInv (iso+ b+) a+)) ≤ₛ-refl)
--                       )
--               ≤⨟  ≤ₛ-cocone {{æ = Approx}} (Iso.fun (iso+ b+) a+) ))
--               ) lt
--           oDataGermMeet (self (<Size  lt')) {{æ = Approx}} {posNoCode = pnc} {cpf = cpf} (r1 (Rec (inr (a+ , a-)))) (r2 (Rec (inr (a+ , a-)))) reflp
--         })
--         -- Exact case: for the negative function, we can just use guarded recursion, since we're under the modality anyways
--         (λ {reflp → do
--           gSelf ← Lself
--           oDataGermMeet gSelf {{æ = Exact}} {posNoCode = pnc} {cpf = cpf} (r1 (Rec (inr (a+ , a-)))) (r2 (Rec (inr (a+ , a-)))) reflp
--           })}
--     f- ← lf-
--       -- oDataGermMeet (self (<Size  lt'))
--       --   (r1 (Rec (a+ , {!!}))) (r2 (Rec (a+ , {!!}))) reflp }
--     let
--       retResponse : Response (interpGermCtor' (GHRec (A+ , A-) D) b+ b-) crec → DataGerm ℓ tyCtor
--       retResponse = λ {
--         -- Strictly positive higher order recursive reference (i.e. function returning self)
--         (Rec (inl x)) → f+ x
--         -- Guarded part of function
--         ; (Rec (inr x)) → f- x
--         ; (Rest x) → rrec x}
--     pure (FC crec retResponse urec)
germFIndMeet {isPos = isPos} (GUnk (A+ , A-) D) (GUnkCode c+ c- iso+ iso- isCode)  b+ b- (FC c1 r1) (FC c2 r2) lt = do
  -- Get the two ⁇-returing functions stored in the positive part of the input
  let
    f1 : A+ b+ → ⁇Ty ℓ
    f1 a+ = ⁇FromW (r1 (inr (Rec (inl a+))))
    f2 : A+ b+ → ⁇Ty ℓ
    f2 a+ = ⁇FromW (r2 (inr (Rec (inl a+))))
    ▹f1 : Σ (A+ b+) (λ a+ → A- b+ a+ b-) → ⁇Ty ℓ
    ▹f1 a+- = ⁇FromW (r1 (inr (Rec (inr a+-))))
    ▹f2 : Σ (A+ b+) (λ a+ → A- b+ a+ b-) → ⁇Ty ℓ
    ▹f2 a+- = ⁇FromW (r2 (inr (Rec (inr a+-))))
  -- Take their meet
  fRet ← liftFun λ a+ → do
    let
      ltRec =
        ≤ₛ-sucMono (smax-mono
          (≤suc ({!!} ≤⨟ smax*-≤-n (Fin.suc (Fin.suc Fin.zero))  ≤⨟ ≤ₛ-cocone (℧Approxed (c+ b+))))
          {!!})
    ⁇result ← oMeet (self (<Size  (<≤ ltRec lt))) C⁇ (f1 a+) (f2 a+) (isPosIrrefut reflp)
    pure (⁇ToW ⁇result)
  -- Get the two ⁇ returning functions from the negative part of the input
  ▹fRet ← liftFun λ (a+ , a-) → caseÆ
    -- Approx case, a- is tt
    (λ {reflp → do
      let
        lt' = ≤ₛ-sucMono
          (smax-mono
            {!!}
            {!!})
      ⁇result ← oMeet (self (<Size  (<≤ lt' lt))) {{æ = Approx}} C⁇ (▹f1 (a+ , Iso.inv (iso- b+ (fst _) b-) tt*)) (▹f2 (a+ , Iso.inv (iso- b+ _ b-) tt*)) (isPosIrrefut reflp)
      Now {!!}})
    -- Exact case, use guarded recursion
    (λ { eq → do
      gSelf ← Lself eq
      ⁇result ← oMeet gSelf C⁇ (▹f1 (a+ , a-)) (▹f2 (a+ , a-)) reflp
      pure (⁇ToW ⁇result) })
    --
    -- pure {!!}
  -- Take the meet of the ⁇ values and the rest, then combine them
  (FC cret rret) ← germFIndMeet D isCode b+ b-
    (FC c1 (Sum.elim (λ r → r1 (inl r)) (λ r → r1 (inr (Rest r)))))
    (FC c2 (Sum.elim (λ r → r2 (inl r)) (λ r → r2 (inr (Rest r)))))
    (<≤ (≤ₛ-sucMono
      (smax-mono (≤suc {!!})
      {!!})) lt)

  --Result contains the positive ⁇ part, the negative ⁇ part, and the rest
  pure (FC cret (Sum.elim
    --TODO does this case actually ever get reached?
    (λ r → rret (inl r))
    ((λ {
-- {C = λ x → AllDataTypes ic ℓ (inext (interpGermCtor' (GUnk (A+ , A-) D) b+ b-) cret (inr (Rec ?)))}
      (Rec r) → Sum.rec
        -- Positive part
        fRet
        -- Negative part
        ▹fRet
        r
      ; (Rest x) → rret (inr x) }) )))
germFIndMeet {tyCtor = tyCtor} (GArg (A+ , A-) D) (GArgCode c+ c- iso+ iso- isCode)  b+ b-
  -- Compute the meet of the strictly positive fields
  (FC ((a+1 , ▹a-1) , c1) r1 ) (FC ((a+2 , ▹a-2) , c2) r2 ) lt = do
  ca+ ← c+ b+ ∋ Iso.fun (iso+ b+) a+1 ⊓ Iso.fun (iso+ b+) a+2
    By argPos (<≤ (≤ₛ-sucMono (smax-mono
       {!!}
       {!!}))
    lt)
  -- Compute the meet of the negative fields
  ca- ← caseÆ
    (λ {reflp → Now (Iso.inv (iso- b+ (Iso.inv (iso+ b+) ca+) b-) tt*)})
    λ eq → do
      ca-1 ← θ eq (Iso.fun (iso- b+ a+1 b-) ▹a-1)
      ca-2 ← θ eq (Iso.fun (iso- b+ a+2 b-) ▹a-2)
      gSelf1 ← Lself eq
      gSelf2 ← Lself eq
      (a-1Cast , lt1) ← oCast gSelf1 (c- b+ a+1 b-) (c- b+ (Iso.inv (iso+ b+) ca+) b-)  ca-1 reflp
      (a-2Cast , lt2) ← oCast gSelf2 (c- b+ a+2 b-) (c- b+ (Iso.inv (iso+ b+) ca+) b-)  ca-2 reflp
      gSelf3 ← Lself eq
      ret ← oMeet gSelf3 (c- b+ (Iso.inv (iso+ b+) ca+) b-) a-1Cast a-2Cast  reflp
      pure (Iso.inv (iso- b+ (Iso.inv (iso+ b+) ca+) b-) (next ret))

  -- Cast the command to the right type
  let lt' = ≤< {!!} lt
  castCom ← castCommand {tyCtor = tyCtor} D isCode (b+ , a+1) (b- , ▹a-1) (b+ , Iso.inv (iso+ b+) ca+) (b- , ca-) c1 lt'
  -- Compute the meet of the rest
  (FC crec rrec) ← germFIndMeet D isCode (b+ , Iso.inv (iso+ b+) ca+) (b- , ca-) (FC castCom {!!}) {!!} {!!}
  -- Put it all together
  pure (FC (
    (Iso.inv (iso+ b+) ca+
    , ca-) ,
    crec) rrec)



-- -- germIndMeet : ∀ {{æ : Æ}} {tyCtor}
-- --   →  {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p cSize}
-- --   → {@(tactic assumption) cpf : if¬Pos ⁇Allowed (S1 ≡p cSize)  (SZ ≡p cSize)}
-- --   → (x y : DataGerm ℓ tyCtor)
-- --   →  smax (germIndSize tyCtor x) (germIndSize tyCtor y) <ₛ size
-- --   → LÆ (DataGerm ℓ tyCtor)
-- -- germIndMeet W℧ y eq = pure W℧
-- -- germIndMeet W⁇ y eq =  pure y
-- -- germIndMeet x W℧ eq = pure W℧
-- -- germIndMeet x W⁇ eq = pure x
-- -- germIndMeet {tyCtor} {posNoCode = posNoCode} {cpf} (Wsup x) (Wsup y) lt
-- --   with (d , x' , xlt) ← germMatch x
-- --   with (dy , y' , ylt) ← germMatch y
-- --   with decFin d dy
-- -- ... | yes reflp = do
-- --   fcRet ← germFIndMeet {posNoCode = posNoCode} {cpf} (germForCtor ℓ tyCtor d) (dataGermIsCode ℓ tyCtor d) tt tt x' y'
-- --     (<ₛ-trans (smax-strictMono xlt ylt) lt)
-- --   pure (dataGermInj fcRet)
-- -- -- Meet is error if they have different data constructors
-- -- ... | no npf = pure W℧
-- --   -- ... | no npf = ?
-- -- -- germIndMeet {tyCtor = tyCtor} x y eq = wInd {!!} {!!} {!!} {!!} x
