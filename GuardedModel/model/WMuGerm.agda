{-# OPTIONS --cubical --guarded --rewriting #-}



-- open import Guarded
open import Cubical.Data.Maybe as Maybe
open import Level
open import Cubical.Relation.Nullary

open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (⊥ to 𝟘)
-- open import Cubical.Data.Prod
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Inductives
open import GuardedAlgebra
open import Cubical.Induction.WellFounded
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Sum as Sum
open import GuardedModality using (later-ext)

open import ApproxExact
open import WMuEq
open import Code
open import WMuEq

open import InductiveCodes

--TODO: don't make ℓ module param
module WMuGerm {{_ : DataTypes}} {{_ : DataGerms}} {{_ : CodesForInductives}} where


-- We only ever attach a size to the approximate part of a computation
-- and we only need this conversion for making a size
private
  instance
    approxÆ : Æ
    approxÆ = Approx

{-# BUILTIN REWRITE _≡_ #-}

abstract
  isoFun : ∀ {A B : Set} (i : Iso A B) → A → B
  isoFun i = Iso.fun i
  isoInv : ∀ {A B : Set} (i : Iso A B) → B → A
  isoInv i = Iso.inv i

  isoFun≡ : ∀ {A B : Set} (i : Iso A B) x → isoFun i x ≡ Iso.fun i x
  isoFun≡ _ _ = refl


  isoRightInv : ∀ {A B : Set} {x} {i : Iso A B} → isoFun i (isoInv i x) ≡ x
  isoRightInv {i = i} = Iso.rightInv i _

  isoLeftInv : ∀ {A B : Set} {x} {i : Iso A B} → isoInv i (isoFun i x) ≡ x
  isoLeftInv {i = i} = Iso.leftInv i _




{-# REWRITE isoRightInv isoLeftInv #-}

rwIso : ∀ {A B : Set} → Iso A B → Iso A B
Iso.fun (rwIso i) = isoFun i
Iso.inv (rwIso i) = isoInv i
Iso.rightInv (rwIso i) x = refl
Iso.leftInv (rwIso i) x = refl

open import Code
-- open import Head
open import Util



---------
-- Data Germ Helpers
-- We use these to extract the strictly-positive parts out of data germ descriptions
-- And erase the negative parts of inhabitants of the described types,
-- which are easier to traverse recursively in a way Agda sees as terminating
---------

open import InductiveCodes

Σ-swap-dist : ∀ {A : Set} {B : A → Set} {C : Set}
  → Iso (Σ (Σ A B) (λ _ → C)) (Σ (A × C) (λ (a , _) → B a))
Iso.fun Σ-swap-dist ((a , b) , c) = (a , c) , b
Iso.inv Σ-swap-dist ((a , c) , b) = (a , b) , c
Iso.rightInv Σ-swap-dist ((a , c) , b) = refl
Iso.leftInv Σ-swap-dist ((a , b) , c) = refl

descSwapIso : ∀ {ℓ} {cI : ℂ ℓ} {sig : IndSig} {cB1 cB2 : ℂ ℓ} (bIso : Iso (ApproxEl cB1) (ApproxEl cB2))
  →  ℂDesc cI cB1 sig
  →  ℂDesc cI cB2 sig
descSwapIso bIso (CEnd i) = CEnd i
descSwapIso bIso (CArg c D cB' x) = CArg (λ x → c (isoInv bIso x)) (descSwapIso theIso D) _ reflp
  where
    theIso = Σ-cong-iso-fst (rwIso bIso)
descSwapIso bIso (CRec j D) = CRec j (descSwapIso bIso D)
descSwapIso bIso (CHRec c j D cB' x) = CHRec (λ x → c (isoInv bIso x)) ((λ x → j (isoInv bIso x))) (descSwapIso bIso D) _ reflp

descAddDeps : ∀ {ℓ} {cI : ℂ ℓ} {sig : IndSig} {cB : ℂ ℓ} (cUnused)
  →  ℂDesc cI cB sig
  →  ℂDesc cI (CΣ cB (λ _ → cUnused)) sig
descAddDeps cUnused (CEnd i) = CEnd i
descAddDeps cUnused (CArg c D cB' x) = CArg (λ (cb , _) → c cb) (descSwapIso theIso (descAddDeps cUnused D)) _ reflp
  where
    theIso = Σ-swap-dist
descAddDeps cUnused (CRec j D) = CRec j (descAddDeps cUnused D)
descAddDeps cUnused (CHRec c j D cB' x) = CHRec (λ (cb , _) → c cb) (λ (cb , _) → j cb) (descAddDeps cUnused D) _ reflp

descAddFunDeps : ∀ {ℓ} {cI : ℂ ℓ} {sig : IndSig} {cB1 : ℂ ℓ} (cB2 : ApproxEl cB1 → ℂ ℓ) (cUnused)
  →  ℂDesc cI cB1 sig
  →  ℂDesc cI (CΣ cB1 (λ x → CΠ (cB2 x) λ _ → cUnused)) sig
descAddFunDeps cB cUnused (CodeModule.CEnd i) = CEnd i
descAddFunDeps cB cUnused (CodeModule.CArg c D cB' x)
  = CArg (λ (cb1 , f) → c cb1) (descSwapIso theIso (descAddFunDeps (λ (x , _) → cB x) cUnused D)) _ reflp
    where
      theIso =
        iso
          (λ ((cb1 , x) , f) → (cb1 , f) , x)
          (λ ((cb1 , f) , x) → (cb1 , x) , f)
          (λ ((cb1 , f) , x) → refl)
          (λ ((cb1 , x) , f) → refl)
descAddFunDeps cB cUnused (CodeModule.CRec j D) = CRec j (descAddFunDeps cB cUnused D)
descAddFunDeps cB cUnused (CodeModule.CHRec c j D cB' x)
  = CHRec
    (λ (cb1 , f) → c cb1)
    (λ (cb1 , f) → j cb1)
    (descAddFunDeps cB cUnused D)
    _
    reflp

posDataGermCode :
  ∀ (ℓ : ℕ)  {sig} {B+ : Set} (cB+ : ℂ ℓ)
  → (Iso B+ (ApproxEl cB+))
  → (D : GermCtor B+ sig)
  → DataGermIsCode ℓ D
  → ℂDesc C𝟙 cB+ sig
posDataGermCode ℓ cB+ bIso GEnd GEndCode = CEnd Gtt
posDataGermCode ℓ cB+ bIso (GArg A+ D hasNeg) (GArgCode c+  iso+ isCode)
  --TODO: handle hasNeg? Not in desc, just in El
  = CArg
    (λ cb → c+ (isoInv bIso cb))
    (posDataGermCode ℓ (CΣ cB+ (λ cb → c+ (isoInv bIso cb))) (Σ-cong-iso (rwIso bIso) (λ b+ → iso+ b+)) D isCode)
    _
    reflp
posDataGermCode ℓ cB+ bIso (GHRec A D) (GHRecCode c+  iso+ isCode)
  = CHRec (λ cb → c+ (isoInv bIso cb)) (λ _ _ → Gtt) (posDataGermCode ℓ cB+ bIso D isCode) _ reflp
posDataGermCode ℓ cB+ bIso (GRec D) (GRecCode isCode)
  = CRec Gtt (posDataGermCode ℓ cB+ bIso D isCode)
-- Unk is just an Arg with return type C⁇
posDataGermCode ℓ cB+ bIso (GUnk A D) (GUnkCode c+  iso+  isCode)
  -- Positive part isn't allowed to depend on values of ⁇
  = CArg (λ cb → CΠ (c+ (isoInv bIso cb)) (λ _ → C⁇)) (descAddFunDeps (λ z → c+ (isoInv bIso z)) C⁇ recDesc) _ reflp
    where
      recDesc = posDataGermCode ℓ cB+ bIso D isCode

posGermForCtor : ∀ ℓ tyCtor → DCtors {ℓ = ℓ} tyCtor C𝟙
posGermForCtor ℓ tyCtor d = posDataGermCode ℓ C𝟙 idIso (preDataGerm ℓ tyCtor d) (dataGermIsCode ℓ tyCtor d)



posDataGermFVal : ∀ {ℓ} (cB+ : ℂ ℓ)  {B+ sig} (tyCtor : CName)
    → (bIso : Iso B+ (ApproxEl cB+))
    → (D : GermCtor B+ sig)
    → (isCode : DataGermIsCode ℓ D)
    → (b+ : B+)
    → (cs : DescFunctor ℓ tyCtor D b+)
    → □ _ (λ (m , _) → Maybe.rec Unit (λ x → tyCtor ≡p x → ℂμ tyCtor (λ d → posGermForCtor ℓ tyCtor d) Gtt) m) (just tyCtor , cs)
    → ℂDescEl
      (posDataGermCode ℓ cB+ bIso D isCode)
      (ℂμ tyCtor
       (λ d₁ →
          posDataGermCode ℓ C𝟙 idIso (preDataGerm ℓ tyCtor d₁)
          (dataGermIsCode ℓ tyCtor d₁)))
      Gtt (Iso.fun bIso b+)
posDataGermFVal cB+ tyCtor bIso GEnd GEndCode b+ (FC com resp) φ = {!!}
posDataGermFVal cB+ tyCtor bIso (GArg A D hasNeg) (GArgCode c+ iso+ isCode) b+ (FC com resp) φ = {!!}
posDataGermFVal cB+ tyCtor bIso (GHRec A D) (GHRecCode c+ iso+ isCode) b+ (FC com resp) φ = {!!}
posDataGermFVal cB+ tyCtor bIso (GRec D) (GRecCode isCode) b+ (FC com resp) φ = {!!}
posDataGermFVal cB+ tyCtor bIso (GUnk A D) (GUnkCode c+ iso+ isCode) b+ (FC com resp) φ = {!!}
    -- → ℂDescEl (posDataGermCode ℓ cB+ bIso D isCode) (λ _ → ℂμ tyCtor (posGermForCtor ℓ tyCtor) Gtt) Gtt (Iso.fun bIso b+)
-- posDataGermFVal cB+ tyCtor bIso GEnd GEndCode b+ b- cs φ = ElEnd tt (tt ⊢ tt ≅ tt)
-- posDataGermFVal {ℓ} {{æ = æ}} cB+ tyCtor bIso (GArg (A+ , A-) D) (GArgCode c+ c- iso+ iso- isCode) b+ b- (FC ((a+ , a-) , com) resp) φ
--   -- This is all just awful rewriting of equalities and such
--     = ElArg (Iso.fun (Iso (iso+ b+)) a+)
--       (subst
--         (λ x → ℂDescEl (posDataGermCode _ (CΣ cB+ (λ ca+ → c+ (isoInv bIso ca+))) theIso D isCode) _ tt x)
--         (( isoFun≡
--           (Σ-cong-iso (rwIso bIso) λ b+ → iso+ b+ Approx) (b+ , approx a+))
--             ∙ ΣPathP (refl , caseÆ (λ {reflp → refl}) (λ {reflp → refl})))
--         recVal)
--       where
--         theIso = Σ-cong-iso (rwIso bIso) λ b+ → iso+ b+ Approx
--         recVal : ℂDescEl
--                    (posDataGermCode _ (CΣ cB+ (λ ca+ → c+ (isoInv bIso ca+))) theIso D
--                     isCode)
--                    (λ _ →
--                       ℂμ tyCtor
--                       (λ d →
--                          posDataGermCode _ C𝟘 idIso
--                          (preDataGerm ℓ tyCtor (▹⁇ ℓ) d)
--                          (dataGermIsCode ℓ tyCtor d))
--                       tt)
--                    tt (isoFun theIso (b+ , approx a+))
--         recVal =
--           posDataGermFVal
--           (CΣ cB+ λ ca+ → c+ (isoInv bIso  ca+))
--           tyCtor
--           theIso
--           D
--           isCode
--           (b+ , approx a+)
--           (b- , approx a-)
--           (FC com (Sum.elim (λ r → resp (inl r)) λ r → resp (inr r)))
--           (Sum.elim (λ r → φ (inl r)) (λ r → φ (inr r)))
-- posDataGermFVal cB+ tyCtor bIso (GHRec A D) (GHRecCode c+ c- iso+ iso- isCode) b+ b- (FC com resp) φ =
--   ElHRec (λ x → φ (inl (Rec (inl (isoInv (Iso (iso+ b+)) x)))) reflp) (posDataGermFVal cB+ tyCtor bIso D isCode b+ b- (FC com (Sum.elim (λ r → resp (inl (Rest r))) λ r → resp (inr r))) (Sum.elim (λ r → φ (inl (Rest r))) (λ r → φ (inr r))))
-- posDataGermFVal cB+ tyCtor bIso (GRec D) (GRecCode isCode) b+ b- (FC com resp) φ
--   = ElRec (φ (inl (Rec tt)) reflp) (posDataGermFVal cB+ tyCtor bIso D isCode b+ b- (FC com (Sum.elim (λ r → resp (inl (Rest r))) λ r → resp (inr r))) (Sum.elim (λ r → φ (inl (Rest r))) (λ r → φ (inr r))))
-- posDataGermFVal {{æ = æ}} cB+ tyCtor bIso (GUnk A D) (GUnkCode c+ c- iso+ iso- isCode) b+ b- (FC com resp) φ
--   = ElArg
--     (caseÆ
--       (λ {reflp → λ x → ⁇FromW {{æ = Approx}} (resp (inr (Rec (inl (Iso.inv (Iso ⦃ æ = Approx ⦄ (iso+ b+)) x)))))})
--       (λ {reflp →
--         (λ x → ⁇FromW ⦃ æ = Approx ⦄ {!x!})
--         , {!!}}))
--     -- (withApproxA (λ x → ⁇FromW {{æ = Approx}} (approx {{æ = Approx}} (resp (inr (Rec (inl (Iso.inv (Iso (iso+ b+)) {!x!}))))))) {!!})
--     {!!}


posDataGermVal :
  (ℓ : ℕ) (tyCtor : CName)
  → DataGerm ℓ tyCtor
  → ℂμ tyCtor (λ d → posDataGermCode ℓ C𝟙 idIso (germForCtor ℓ tyCtor d) (dataGermIsCode ℓ tyCtor d)) Gtt
posDataGermVal ℓ tyCtor germVal = recFun reflp
  where
    recFun =
      DataGermRec'
        (Maybe.rec Unit (λ x → tyCtor ≡p x → ℂμ tyCtor (λ d → posDataGermCode ℓ C𝟙 idIso (germForCtor ℓ tyCtor d) (dataGermIsCode ℓ tyCtor d)) Gtt))
        (λ _ _ → tt)
        (λ {d y φ reflp → Cinit d (posDataGermFVal C𝟙 tyCtor idIso (preDataGerm ℓ tyCtor d) (dataGermIsCode ℓ tyCtor d) Gtt y φ)})
        (λ { nothing → tt , tt ; (just x) → (λ _ → Cμ⁇) , λ _ → Cμ⁇})
        germVal
--     -- wRec {X = λ { nothing → Unit ; (just x) → x ≡p tyCtor → ℂμ tyCtor (λ d → posDataGermCode ℓ idIso (germForCtor ℓ tyCtor d) (dataGermIsCode ℓ tyCtor d)) true}}
--     --   (λ { {nothing} x₁ → tt ; {just _} (FC (d , com) response) reflp → Cinit d (posDataGermFVal tyCtor idIso _ _ {!!} tt {!FC com response!} {!!} )})
--     --   (λ { nothing → tt , tt ; (just x) → (λ {reflp → Cμ⁇}) , λ {reflp → Cμ℧}}) x
