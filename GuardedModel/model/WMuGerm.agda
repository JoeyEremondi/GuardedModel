{-# OPTIONS --cubical --guarded  #-}



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

descSwapIso : ∀ {ℓ}  {sig : IndSig} {cB1 cB2 : ℂ ℓ} (bIso : Iso (ApproxEl cB1) (ApproxEl cB2))
  →  ℂDesc cB1 sig
  →  ℂDesc cB2 sig
descSwapIso bIso (CEnd) = CEnd
descSwapIso bIso (CArg c D (CΣ cB1 _) reflp) = CArg (λ x → c (Iso.inv bIso x)) (descSwapIso (Σ-cong-iso bIso (λ x → substPath (λ y → Iso (El (c x)) (El (c y))) (symPath (Iso.leftInv bIso x)) idIso)) D) _ reflp
descSwapIso bIso (CRec D) = CRec (descSwapIso bIso D)
descSwapIso bIso (CHRec c D cB' x) = CHRec (λ x → c (Iso.inv bIso x)) (descSwapIso bIso D) _ reflp

elSwapIso :
  ∀ {ℓ}  {sig : IndSig} {cB1 cB2 : ℂ ℓ} (bIso : Iso (ApproxEl cB1) (ApproxEl cB2))
  → (X : Set)
  →  (D : ℂDesc cB1 sig)
  → (b+ : ApproxEl cB1)
  →  ℂDescEl D X b+
  → ℂDescEl (descSwapIso bIso D) X (Iso.fun bIso b+)
elSwapIso bIso X CodeModule.CEnd b+ ElEnd = ElEnd
elSwapIso {cB1 = cB1} {cB2 = cB2} bIso X (CodeModule.CArg c D .(CΣ _ c) .reflp) b+ (ElArg a x) = ElArg (subst (λ x → El (c x)) (sym (Iso.leftInv bIso b+)) a)
  (subst (λ pr → ℂDescEl' X (CΣ cB2 (λ x₁ → c (Iso.inv bIso x₁)) ) (descSwapIso theIso D) pr)
    (ΣPathP (reflc , congPath
                       (transp (λ i → ApproxEl (c (Iso.leftInv bIso b+ (~ i)))) i0) (transportRefl a)))
    recVal)
  where
    theIso = Σ-cong-iso bIso (λ x → substPath (λ y → Iso (El (c x)) (El (c y))) (symPath (Iso.leftInv bIso x)) idIso)
    recVal : ℂDescEl' X (CΣ cB2 (λ x₁ → c (Iso.inv bIso x₁)) ) (descSwapIso theIso D) (Iso.fun theIso (b+ , a))
    recVal = elSwapIso theIso X D (b+ , a) x
elSwapIso bIso X (CodeModule.CRec D) b+ (ElRec x x₁) = ElRec x (elSwapIso bIso X D b+ x₁)
elSwapIso bIso X (CodeModule.CHRec c D .(CΣ _ c) .reflp) b+ (ElHRec x x₁) = ElHRec (subst (λ b → El (c b) → X) (sym (Iso.leftInv bIso b+)) x) (elSwapIso bIso X D b+ x₁)

descAddDeps : ∀ {ℓ}  {sig : IndSig} {cB : ℂ ℓ} (cUnused)
  →  ℂDesc cB sig
  →  ℂDesc (CΣ cB (λ _ → cUnused)) sig
descAddDeps cUnused (CEnd) = CEnd
descAddDeps cUnused (CArg c D cB' x) = CArg (λ (cb , _) → c cb) (descSwapIso theIso (descAddDeps cUnused D)) _ reflp
  where
    theIso = Σ-swap-dist
descAddDeps cUnused (CRec D) = CRec (descAddDeps cUnused D)
descAddDeps cUnused (CHRec c D cB' x) = CHRec (λ (cb , _) → c cb) (descAddDeps cUnused D) _ reflp

descAddFunDeps : ∀ {ℓ}  {sig : IndSig} {cB1 : ℂ ℓ} (cB2 : ApproxEl cB1 → ℂ ℓ) (cUnused)
  →  ℂDesc cB1 sig
  →  ℂDesc (CΣ cB1 (λ x → CΠ (cB2 x) λ _ → cUnused)) sig
descAddFunDeps cB cUnused (CodeModule.CEnd) = CEnd
descAddFunDeps cB cUnused (CodeModule.CArg c D cB' x)
  = CArg (λ (cb1 , f) → c cb1) (descSwapIso theIso (descAddFunDeps (λ (x , _) → cB x) cUnused D)) _ reflp
    where
      theIso =
        iso
          (λ ((cb1 , x) , f) → (cb1 , f) , x)
          (λ ((cb1 , f) , x) → (cb1 , x) , f)
          (λ ((cb1 , f) , x) → refl)
          (λ ((cb1 , x) , f) → refl)
descAddFunDeps cB cUnused (CodeModule.CRec D) = CRec (descAddFunDeps cB cUnused D)
descAddFunDeps cB cUnused (CodeModule.CHRec c D cB' x)
  = CHRec
    (λ (cb1 , f) → c cb1)
    (descAddFunDeps cB cUnused D)
    _
    reflp


elAddFunDeps : ∀ {ℓ}  {sig : IndSig} {cB1 : ℂ ℓ} (cB2 : ApproxEl cB1 → ℂ ℓ) (cUnused)
  → (X : Set)
  →  (D : ℂDesc cB1 sig)
  → (b+ : ApproxEl (CΣ cB1 (λ x → CΠ (cB2 x) (λ _ → _))))
  →  ℂDescEl D X (fst b+)
  → ℂDescEl (descAddFunDeps cB2 cUnused D) X b+
elAddFunDeps cB cUnused X CodeModule.CEnd (fst₁ , snd₁) ElEnd = ElEnd
elAddFunDeps cB cUnused X (CodeModule.CArg c D .(CΣ _ c) .reflp) (fst₁ , snd₁) (ElArg a x) = ElArg a (elSwapIso _ X _ ((fst₁ , approx a) , snd₁) recVal)
  where
    recVal = elAddFunDeps (λ y → cB (fst y)) cUnused X D ((fst₁ , approx a) , snd₁ ) x
elAddFunDeps cB cUnused X (CodeModule.CRec D) (fst₁ , snd₁) (ElRec x x₁) = ElRec x (elAddFunDeps cB cUnused X D (fst₁ , snd₁) x₁)
elAddFunDeps cB cUnused X (CodeModule.CHRec c D .(CΣ _ c) .reflp) (fst₁ , snd₁) (ElHRec x x₁) = ElHRec x (elAddFunDeps cB cUnused X D (fst₁ , snd₁) x₁)

posDataGermCode :
  ∀ (ℓ : ℕ)  {sig} {B+ : Set} (cB+ : ℂ ℓ)
  → (bFun : (ApproxEl cB+) → B+)
  → (D : GermCtor B+ sig)
  → DataGermIsCode ℓ D
  → ℂDesc cB+ sig
posDataGermCode ℓ cB+ bIso GEnd GEndCode = CEnd
posDataGermCode ℓ cB+ bFun (GArg A+ D false) (GArgCode c+  iso+ isCode)
  --TODO: handle hasNeg? Not in desc, just in El
  = CArg
    (λ cb → c+ (bFun cb))
    (posDataGermCode ℓ (CΣ cB+ (λ cb → c+ (bFun cb))) (λ (b , a) → bFun b , Iso.inv (iso+ (bFun b)) a) D isCode)
    _
    reflp
posDataGermCode ℓ cB+ bFun (GArg A+ D true) (GArgCode c+  iso+ isCode)
  --TODO: handle hasNeg? Not in desc, just in El
  = CArg
    (λ cb → CΣ (c+ (bFun cb)) (λ _ → C⁇))
    (posDataGermCode ℓ (CΣ cB+ (λ cb → CΣ (c+ (bFun cb)) (λ _ → C⁇))) (λ (b , (a , _)) → ( bFun b , Iso.inv (iso+ _) a )) D isCode)
      -- (posDataGermCode ℓ (CΣ cB+ (λ cb → c+ (bFun cb))) (Σ-cong-iso bIso (λ b+ → substPath (λ y → Iso (A+ b+) (El (c+ y))) (sym (Iso.leftInv bIso b+)) (iso+ b+))) D isCode) ?
    _
    reflp
posDataGermCode ℓ cB+ bFun (GHRec A D) (GHRecCode c+  iso+ isCode)
  = CHRec (λ cb → c+ (bFun cb)) (posDataGermCode ℓ cB+ bFun D isCode) _ reflp
posDataGermCode ℓ cB+ bFun (GRec D) (GRecCode isCode)
  = CRec (posDataGermCode ℓ cB+ bFun D isCode)
-- Unk is just an Arg with return type C⁇
posDataGermCode ℓ cB+ bFun (GUnk A D) (GUnkCode c+  iso+  isCode)
  -- Positive part isn't allowed to depend on values of ⁇
  = CArg (λ cb → CΠ (c+ (bFun cb)) (λ _ → C⁇)) (descAddFunDeps (λ z → c+ (bFun z)) C⁇ recDesc) _ reflp
    where
      recDesc = posDataGermCode ℓ cB+ bFun D isCode
-- posDataGermCode ℓ cB+ bFun (GUnk A D) (GUnkCode c+  iso+  isCode)
--   -- Positive part isn't allowed to depend on values of ⁇
--   = CArg (λ cb → CΠ (c+ (bFun cb)) (λ _ → C⁇)) (descAddFunDeps (λ z → c+ (bFun z)) C⁇ recDesc) _ reflp
--     where
--       recDesc = posDataGermCode ℓ cB+ bFun D isCode

posGermForCtor : ∀ ℓ tyCtor → DCtors {ℓ = ℓ} tyCtor
posGermForCtor ℓ tyCtor d = posDataGermCode ℓ C𝟙 (λ _ → Gtt) (preDataGerm ℓ tyCtor d) (dataGermIsCode ℓ tyCtor d)



posDataGermFVal : ∀ {ℓ} (cB+ : ℂ ℓ)  {B+ sig} (tyCtor : CName)
    → (bFun : (ApproxEl cB+) → B+)
    → (D : GermCtor B+ sig)
    → (isCode : DataGermIsCode ℓ D)
    → (b+ : ApproxEl cB+)
    → (cs : DescFunctor ℓ tyCtor D (bFun b+))
    → □ _ (λ (m , _) → Maybe.rec Unit (λ x → tyCtor ≡p x → ℂμ tyCtor (λ d → posGermForCtor ℓ tyCtor d) ) m) (just tyCtor , cs)
    → ℂDescEl
      (posDataGermCode ℓ cB+ bFun D isCode)
      (ℂμ tyCtor
       (λ d₁ →
          posDataGermCode ℓ C𝟙 (λ _ → Gtt) (preDataGerm ℓ tyCtor d₁)
          (dataGermIsCode ℓ tyCtor d₁)))
      b+
posDataGermFVal cB+ tyCtor bFun GEnd GEndCode b+ (FC com resp) φ = ElEnd
posDataGermFVal cB+ tyCtor bFun (GArg A D false) (GArgCode c+ iso+ isCode) b+ (FC (a , com) resp) φ =
  ElArg (Iso.fun (iso+ (bFun b+)) a)
    (posDataGermFVal (CΣ cB+ (λ cb → c+ (bFun cb))) tyCtor _ D isCode (b+ , approx (Iso.fun (iso+ (bFun b+)) a))
    (substPath (λ b → DescFunctor _ tyCtor D (bFun b+ , b)) (sym (Iso.leftInv (iso+ _) a))
      (FC com (Sum.elim (λ r → resp (inl r)) (λ r → resp (inr (Rest r))))))
    (Sum.elim (λ r → φ (inl (substPath
                               (λ (pr : Σ (A (bFun b+)) (λ a → GermCommand D (bFun b+ , a))) →
                                  GermResponse D (bFun b+ , fst pr) (snd pr))
                               (ΣPathP (Iso.leftInv (iso+ (bFun b+)) a ,
                                 symP (transport-filler _ _))
                                 ) r))) λ b → tt))
posDataGermFVal cB+ tyCtor bFun (GArg A D true) (GArgCode c+ iso+ isCode) b+ (FC (a , com) resp) φ =
  ElArg (Iso.fun (iso+ (bFun b+)) a , ⁇FromW (resp (inr (Rec tt))))
    (posDataGermFVal (CΣ cB+ (λ cb → CΣ (c+ (bFun cb)) (λ _ → C⁇))) tyCtor _ D isCode
      (b+ ,
          approx (Iso.fun (iso+ (bFun b+)) a , ⁇FromW (resp (inr (Rec tt)))))
            (substPath (λ b → DescFunctor _ tyCtor D (bFun b+ , b)) (sym (Iso.leftInv (iso+ _) a))
              (FC com (Sum.elim (λ r → resp (inl r)) (λ r → resp (inr (Rest r))))))
    (Sum.elim (λ r → φ (inl (substPath
                               (λ (pr : Σ (A (bFun b+)) (λ a → GermCommand D (bFun b+ , a))) →
                                  GermResponse D (bFun b+ , fst pr) (snd pr))
                               (ΣPathP (Iso.leftInv (iso+ (bFun b+)) a , symP (transport-filler _ _))
                                 -- (Iso.leftInv (iso+ (bFun b+)) a , symP (transport-filler (λ i →
                                 --                                                                     GermCommand D (bFun b+ , Iso.leftInv (iso+ (bFun b+)) a (~ i))) (snd (maybeIrrefute (a , com)))))
                               ) r))) λ b → tt))
posDataGermFVal cB+ tyCtor bFun (GRec D) (GRecCode isCode) b+ (FC com resp) φ
  = ElRec (φl reflp)
    (posDataGermFVal cB+ tyCtor bFun D isCode b+ (FC com (Sum.elim (λ r → resp (inl (Rest r))) (λ r → resp (inr r))))
    (Sum.elim (λ r → φ (inl (Rest r))) (λ _ → tt)))
    where
      φl = φ (inl (Rec tt))
posDataGermFVal cB+ tyCtor bFun (GHRec A D) (GHRecCode c+ iso+ isCode) b+ (FC com resp) φ =
  ElHRec theFun (posDataGermFVal cB+ tyCtor bFun D isCode b+
    (FC com (Sum.elim (λ r → resp (inl (Rest r))) (λ r → resp (inr r))))
    (Sum.elim (λ r → φ (inl (Rest r))) (λ r → φ (inr r))))
    where
      theFun : (cb+ : El (c+ (bFun b+))) → _
      theFun cb+ = φl reflp
        where
          φl = φ (inl (Rec (Iso.inv (iso+ (bFun b+)) cb+)))
posDataGermFVal cB+ tyCtor bFun (GUnk A D) (GUnkCode c+ iso+ isCode) b+ (FC com resp) φ =
  ElArg (λ x → ⁇FromW (resp (inr (Rec (Iso.inv (iso+ (bFun b+)) x)))))
    (elAddFunDeps (λ z → c+ (bFun z)) C⁇ _ _ (b+ ,
                                                     approx
                                                     (λ x → ⁇FromW (resp (inr (Rec (Iso.inv (iso+ (bFun b+)) x)))))) recVal)
  where
    recVal = posDataGermFVal cB+ tyCtor bFun D isCode b+
      (FC com (Sum.elim (λ r → resp (inl r)) (λ r → resp (inr (Rest r)))))
      (Sum.elim (λ r → φ (inl r)) (λ r → φ (inr (Rest r))))

posDataGermVal :
  (ℓ : ℕ) (tyCtor : CName)
  → DataGerm ℓ tyCtor
  → ℂμ tyCtor (λ d → posDataGermCode ℓ C𝟙 (λ _ → Gtt) (germForCtor ℓ tyCtor d) (dataGermIsCode ℓ tyCtor d))
posDataGermVal ℓ tyCtor germVal = recFun reflp
  where
    recFun =
      DataGermRec'
        (Maybe.rec Unit (λ x → tyCtor ≡p x → ℂμ tyCtor (λ d → posDataGermCode ℓ C𝟙 (λ _ → Gtt) (germForCtor ℓ tyCtor d) (dataGermIsCode ℓ tyCtor d))))
        (λ _ _ → tt)
        (λ {d y φ reflp → Cinit d (posDataGermFVal C𝟙 tyCtor (λ _ → Gtt) (preDataGerm ℓ tyCtor d) (dataGermIsCode ℓ tyCtor d) Gtt y φ)})
        (λ { nothing → tt , tt ; (just x) → (λ _ → Cμ⁇) , λ _ → Cμ⁇})
        germVal
