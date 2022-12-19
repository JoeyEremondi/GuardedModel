

{-# OPTIONS --cubical --guarded -v term:50 #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
-- open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat as Nat
import Cubical.Data.Nat.Order as Nat
import Cubical.Induction.WellFounded as Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool
-- open import Cubical.Data.Equality
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import UnkGerm
open import GuardedAlgebra
import GuardedModality as G
open import Cubical.Induction.WellFounded
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import InductiveCodes
open import W
-- open import Cubical.Data.Equality using (ptoc)

open import ApproxExact


-- open import InductiveCodes
open import Cubical.Foundations.Transport


-- Brouwer Tree ordinals
-- Based on the presentation by Kraus, Forsburg and Xu
-- https://arxiv.org/abs/2104.02549

-- The main difference is that we allow the limit over the elements of any code type, not just natural numbers

open import InductiveCodes
module CodeSize {{_ : DataTypes}} {{_ : DataGerms}} {{_ : CodesForInductives }} where


open import SizeOrdMultiMax public





open import Code
open import Head
open import Util

open import SizeOrd -- ℂ El ℧ C𝟙 refl

record CodeSizeF (ℓ : ℕ) : Set  where
  constructor codeSizeF
  field
    smallerCodeSize : {{inst : 0< ℓ}} → ℂ-1 (SmallerCodeAt ℓ ) → Size
    smallerElSize : {{æ : Æ }} → {{inst : 0< ℓ}} → (c : ℂ-1 (SmallerCodeAt ℓ)) → El-1 (SmallerCodeAt ℓ) c → Size

  -- germSize {ℓ} tyCtor = wInd (λ _ → LargeSize) (germDescFSize tyCtor (GArg (DName tyCtor) (dataGerm ℓ tyCtor (▹⁇ ℓ)))) LO1 LO1

  CFin : ∀ (n : ℕ) → ℂ 0
  CFin ℕ.zero = C℧
  CFin (ℕ.suc n) = CΣ C𝟙 (λ {℧𝟙  → C℧ ; Gtt → CFin n})


  fromCFin : ∀ {n} → El {{æ = Approx}} (CFin n) → Fin (ℕ.suc n)
  fromCFin {ℕ.zero} _ = Fin.zero
  fromCFin {ℕ.suc n} (℧𝟙 , rest) = Fin.zero
  fromCFin {ℕ.suc n} (Gtt , rest) = Fin.suc (fromCFin rest)


  toCFin : ∀ {n} → Fin (ℕ.suc n) → El {{æ = Approx}} (CFin n)
  toCFin {n = ℕ.zero} x = ℧𝟘
  toCFin {n = ℕ.suc n} Fin.zero = ℧𝟙 , ℧𝟘
  toCFin {n = ℕ.suc n} (Fin.suc x) = Gtt , toCFin x

  fromToCFin : ∀ {n} (x : Fin (ℕ.suc n)) → fromCFin (toCFin x) ≡p x
  fromToCFin {ℕ.zero} Fin.zero = reflp
  fromToCFin {ℕ.suc n} Fin.zero = reflp
  fromToCFin {ℕ.suc n} (Fin.suc x) rewrite fromToCFin x = reflp



  -- germFIndSize : ∀ {{æ : Æ}}  {B+ B- sig} (tyCtor : CName) → (D : GermCtor B+ B- sig)
  --   → (DataGermIsCode ℓ D)
  --   → (b+ : B+)
  --   → (b- : B- b+)
  --   → (cs : DescFunctor ℓ tyCtor D b+ b-)
  --   → □ _ (λ _ → Size) (just tyCtor , cs)
  --   → Size

  -- germUnkFSize : ∀ {{æ : Æ}} → (x : GermUnkFunctor ℓ) → □ _ (λ _ → Size) (nothing , x) → Size


  -- germUnkFSize (FC (HΠ , arg) f) φ = S↑ (SLim C⁇ helper)
  --   where
  --     helper : ApproxEl {ℓ = ℓ} C⁇ → Size
  --     helper x = φ (transportPath (symPath ⁇Wrap≡) (next fx))
  --       where
  --         fx = apply⁇Fun (λ x → ⁇FromW (f x)) (exact {ℓ = ℓ} {c = C⁇} x)
  -- germUnkFSize (FC (HΣ , arg) resp) φ = S↑ (smax (φ true ) (φ false))
  -- germUnkFSize (FC (H≅ , arg) resp) φ = S↑ (φ tt)
  -- germUnkFSize (FC (H𝟙 , arg) resp) φ = S1
  -- germUnkFSize (FC (HType , arg) resp) φ  = S↑ (smallerCodeSize ⦃ ℂ-1>0 arg ⦄ arg) -- S↑ (smallerCodeSize ⦃ ? ⦄ arg)
  -- germUnkFSize (FC (HCumul , (c , x)) resp) φ =  S↑ (smallerElSize {{inst = ℂ-1>0 c}} c x)
  -- germUnkFSize (FC (HCtor x , arg) resp) φ = {!!}

  -- allDataSize : ∀ {{ æ : Æ }}  {mc : Maybe CName} →  AllDataTypes ℓ mc → Size
  -- allDataSize = DataGerm Size germUnkFSize (λ d x → germFIndSize _ (germForCtor ℓ _ d) (dataGermIsCode ℓ _ d) tt tt x) (λ _ → S1 , S1)




  -- germFIndSize tyCtor GEnd GEndCode b+ b- (FC com k) φ = S1
  -- germFIndSize tyCtor (GArg (A+ , A-) D) (GArgCode c+ c- iso+ iso- isCode) b+ b- (FC ((a+ , a-) , com) k) φ
  --   = S↑ (germFIndSize tyCtor D isCode (b+ , a+) (b- , a-) (FC com (Sum.elim (λ r → k (inl r)) λ r → k (inr r)))  φ)
  -- germFIndSize tyCtor (GHRec (A+ , A-) D) (GHRecCode c+ c- iso+ iso- isCode) b+ b- (FC com k) φ
  --   = S↑ (SLim (c+ b+) helper)
  --     where
  --     helper : (a+ : El (c+ b+))  → Size
  --     helper a+  = smax*
  --       -- We only do sizes on the part that isn't hidden behind guardedness
  --       -- For the guarded part, we take the size at ℧, for the approx case this is the only argument
  --       -- (φ (Rec (inl ac+)))
  --       (φ (inl (Rec (inl ac+)))
  --       -- In approx case, only one value to give
  --       -- In exact case, we use ℧ trivially (but we don't actually need this, we just use fix to recur in these cases)
  --       ∷ φ (inl (Rec (inr (ac+ , Iso.inv (iso- b+ ac+ b-) (caseÆ (λ {reflp → tt*}) (λ {reflp → G.next (℧ ⦃ æ = Exact ⦄ (c- b+ ac+ b-))}))))))
  --       ∷ (germFIndSize tyCtor D isCode b+ b-
  --         (FC com (Sum.elim (λ r → k (inl (Rest r))) λ r → k (inr r)))
  --         (Sum.elim (λ r → φ (inl (Rest r))) (λ r → φ (inr r))))
  --       ∷ [])
  --       where
  --         ac+ : A+ b+
  --         ac+ = Iso.inv (iso+ b+) a+
  -- germFIndSize tyCtor (GRec D) (GRecCode isCode) b+ b- (FC com k) φ
  --   = S↑ (smax
  --     (φ (inl (Rec tt)))
  --     (germFIndSize tyCtor D isCode b+ b-
  --       (FC com (Sum.elim (λ r → k (inl (Rest r))) (λ r → k (inr r))) )
  --       (Sum.elim (λ r → φ (inl (Rest r))) (λ r → φ (inr r)))))
  -- germFIndSize tyCtor (GUnk (A+ , A-) D) (GUnkCode c+ c- iso+ iso- isCode) b+ b- (FC com k) φ
  --   = S↑ (SLim (c+ b+) helper)
  --     where
  --     helper : (a+ : El (c+ b+))  → Size
  --     helper a+  = smax*
  --       -- We only do sizes on the part that isn't hidden behind guardedness
  --       -- For the guarded part, we take the size at ℧, for the approx case this is the only argument
  --       -- (φ (Rec (inl ac+)))
  --       (φ (inr (Rec (inl ac+)))
  --       -- In approx case, only one value to give
  --       -- In exact case, we use ℧ trivially (but we don't actually need this, we just use fix to recur in these cases)
  --       ∷ φ (inr (Rec (inr (ac+ , Iso.inv (iso- b+ ac+ b-) (caseÆ (λ {reflp → tt*}) (λ {reflp → G.next (℧ ⦃ æ = Exact ⦄ (c- b+ ac+ b-))}))))))
  --       ∷  (germFIndSize tyCtor D isCode b+ b-
  --            (FC com (Sum.elim (λ r → k (inl r)) (λ r → k (inr (Rest r)))) )
  --            (Sum.elim (λ r → φ (inl r)) (λ r → φ (inr (Rest r)))))
  --       ∷ [])
  --       where
  --         ac+ : A+ b+
  --         ac+ = Iso.inv (iso+ b+) a+





  FinLim : ∀ {n} → (Fin n → Size) → Size
  FinLim {ℕ.zero} f = SZ
  FinLim {ℕ.suc n} f = SLim (CFin n) (λ x → f (fromCFin x))


  DLim : ∀ (tyCtor : CName) → ((d : DName tyCtor) → Size) → Size
  DLim tyCtor f = FinLim f

  FinLim-cocone : ∀ {n} → (f : ( Fin n) → Size) → (d : Fin n) → f d ≤ₛ FinLim f
  FinLim-cocone {ℕ.suc n} f d = pSubst (λ x → f d ≤ₛ f x) (pSym (fromToCFin d)) ≤ₛ-refl ≤⨟ ≤ₛ-cocone (toCFin d)

  extFinLim : ∀ {n} → (f1 f2 : (d : Fin n) → Size) → (∀ d → f1 d ≤ₛ f2 d) → (FinLim f1) ≤ₛ (FinLim f2)
  extFinLim {n = ℕ.zero} f1 f2 lt = ≤ₛ-Z
  extFinLim  {ℕ.suc n} f1 f2 lt = ≤ₛ-extLim ⦃ æ = Approx ⦄ (λ k → lt (fromCFin k))

  smax-FinLim2 : ∀ {n} → (f1 f2 : (d : Fin n) → Size) →  FinLim (λ d1 → FinLim (λ d2 → smax (f1 d1) (f2 d2))) ≤ₛ smax (FinLim f1) (FinLim f2)
  smax-FinLim2 {ℕ.zero} f1 f2 = ≤ₛ-Z
  smax-FinLim2 {ℕ.suc n} f1 f2 = smax-lim2L (λ z → f1 (fromCFin z)) (λ z → f2 (fromCFin z))


  -- dataGermSize : ∀ {{æ : Æ}} (tyCtor : CName) → DataGerm ℓ tyCtor → Size
  -- dataGermSize tyCtor x = allDataSize x
  -- dataGermSize tyCtor (Wsup (FC (d , com) resp)) =
  --   germIndSize tyCtor (germForCtor ℓ tyCtor d) (dataGermIsCode ℓ tyCtor d) tt tt
  --     (FC com (Sum.elim (λ r → resp (inl r)) (λ r → resp (inr r))))
  -- dataGermSize tyCtor W⁇ = S1
  -- dataGermSize tyCtor W℧ = S1

  codeSize : ℂ ℓ → Size
  -- descSize : ∀  { sig} →  {cB : ℂ ℓ} → ℂDesc cB sig → Size


  codeSize C⁇ = S1
  codeSize C℧ = S1
  codeSize C𝟘 = S1
  codeSize C𝟙 = S1
  codeSize CType = S1
  codeSize (CΠ dom cod) =
    S↑ (smax
      ( (codeSize dom))
      ( (SLim dom λ x →  (codeSize (cod x)))))
  codeSize (CΣ dom cod) =
    S↑ (smax
      ( (codeSize dom))
      (  (SLim dom λ x →  (codeSize (cod x)))))
  codeSize  (C≡ c x y) = S↑ ( (codeSize c))
  codeSize (Cμ tyCtor c D x) = S↑ (DLim tyCtor λ d → smax (codeSize (ℂCommand (D d))) (SLim (ℂCommand (D d)) (λ com → codeSize (ℂHOResponse (D d) com))))
    -- S↑ (smax
    --   ( (codeSize c))
    --   ( (DLim tyCtor λ d → descSize (D d))))
  codeSize (CCumul {{inst = inst}} c) = S↑ (smallerCodeSize c)






  private
    instance
      approxÆ : Æ
      approxÆ = Approx

  -- germUnkSize : (x : WUnk {{æ = Approx}} ℓ) → Size
  ⁇Size : ∀ {{ æ : Æ}} → ⁇Ty ℓ → Size
  elSize : ∀ {{æ : Æ}} {c : ℂ ℓ} → CodeSizer c → El c → Size
  -- ▹elSize : ∀ {ℓ} (c : ℂ ℓ) → ▹El c → Size
  -- CμSize : ∀   {tyCtor : CName} (D : DCtors {ℓ = ℓ} tyCtor)  → ℂμ tyCtor D → Size
  -- CElSize : ∀ {sig} {cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cB sig) (E : DCtors {ℓ = ℓ} tyCtor) {b} → ℂDescEl D (ℂμ tyCtor E) b → Size


  -- germUnkSize (Wsup (FC (HΠ , args) f)) = S↑ (germUnkSize (f tt*))
  -- germUnkSize (Wsup (FC (HΣ , args) resp)) = S↑ (smax (germUnkSize (resp true)) (germUnkSize (resp false)))
  -- germUnkSize (Wsup (FC (H≅ , args) resp)) = S↑ (germUnkSize (resp tt))
  -- germUnkSize (Wsup (FC (H𝟙 , args) resp)) = S1
  -- germUnkSize (Wsup (FC (HType , args) resp)) =  S↑ (smallerCodeSize ⦃ ℂ-1>0 args ⦄ args) -- S↑ (smallerCodeSize ⦃ ? ⦄ arg)
  -- germUnkSize (Wsup (FC (HCumul , (c , x)) resp)) = S↑ (smallerElSize {{æ = Approx}} {{inst = ℂ-1>0 c}} c x)
  -- --TODO fix this one
  -- germUnkSize (Wsup (FC (HCtor tyCtor , args) resp)) = S1 --S↑ (CμSize _ (posDataGermVal ℓ tyCtor (resp tt)))
  -- germUnkSize W⁇ = S1
  -- germUnkSize W℧ = S1

  --TODO
  ⁇Size ⁇℧ = S1
  ⁇Size ⁇⁇ = S1
  ⁇Size ⁇𝟙 = S1
  ⁇Size (⁇Type x) = S1
  ⁇Size (⁇Cumul c x) = S1
  ⁇Size (⁇Π x) = S1
  ⁇Size (⁇Σ x) = S1
  ⁇Size (⁇≡ x) = S1
  ⁇Size (⁇μ tyCtor x) = {!!} --S↑ (CμSize _ (posDataGermVal ℓ tyCtor x))

  elSize {{æ = æ}} (CS⁇ codes pf) x = ⁇Size {{æ = æ}} x --germUnkSize (⁇ToW {{æ = Approx}} (approx {c = CS⁇ {ℓ = ℓ}} x))
  elSize CS℧ x = S1
  elSize CS𝟘 x = S1
  elSize CS𝟙 x = S1
  elSize (CSType {{inst = inst}}) x = S↑ (smallerCodeSize x)
  elSize {{æ = æ}} {CΠ dom cod} (CSΠ sdom scod) f = S↑ (SLim dom (λ x → elSize {{æ = æ}} (scod x) (substPath (λ x → El (cod x)) (approxExact≡ x) (f (exact x))) ))
  elSize {{æ = æ}} (CSΣ dom cod) (x , y) = S↑ (smax (elSize {{æ = æ}} dom x) (elSize {{æ = æ}} (cod (approx x)) y)) -- S↑ (smax (elSize dom (exact x)) (elSize (cod (approx x)) y))
  elSize (CS≡ c) (x ⊢ x₁ ≅ y) = S↑ (elSize {{Approx}} c x)
  elSize {c = Cμ tyCtor cI D i} (CSμ coms ress) (Wsup (FC (d , com) res)) = S↑ (smax* (elSize (coms d) com ∷ (FinLim λ n → elSize {!!} (res (inl n))) ∷ (SLim (ℂCommand (D d)) λ com → SLim (ℂHOResponse (D d) com) λ x → elSize {!CSμ coms ress!} (res (inr (exact _ x)))) ∷ [])) -- S↑ (CSμSize D ( Iso.inv CSμWiso (approx {ℓ = ℓ} {c = CSμ tyCtor cI D i} x) ))
  elSize {c = Cμ tyCtor cI D i} (CSμ coms ress) W⁇ = S1
  elSize {c = Cμ tyCtor cI D i} (CSμ coms ress) W℧ = S1
  elSize (CSCumul {{inst = inst}}) x = smallerElSize _ x --elSize c x

  -- CμSize D (Cinit d x) = S↑ (CElSize (D d) D x)
  -- CμSize D Cμ⁇ = S1
  -- CμSize D Cμ℧ = S1

  -- CElSize  .CEnd E  (ElEnd) = S1
  -- CElSize (CArg c D _ _) E {b = b} (ElArg a x) = S↑ (smax (elSize {{æ = Approx}} (c b) a) (CElSize D E x))
  -- CElSize (CRec D) E (ElRec x x₁) = S↑ (smax (CμSize E x) (CElSize D E x₁))
  -- CElSize (CHRec c D _ _) E {b = b} (ElHRec f x) = S↑ (SLim (c b) λ a → smax (CμSize E (f a)) (CElSize D E x))


--TODO uncomment after here

-- SizeMod : ∀ {ℓ} → CodeSizeF ℓ
-- SizeMod {ℕ.zero} = codeSizeF (λ { {{inst = ()}} }) (λ { {{inst = ()}} })
-- SizeMod {ℕ.suc ℓ} = codeSizeF
--       (λ {{inst = suc<}} → CodeSizeF.codeSize (SizeMod {ℓ}))
--       (λ { {{inst = suc<}}  → CodeSizeF.elSize (SizeMod {ℓ})})

-- module SM {ℓ} where
--   open CodeSizeF (SizeMod {ℓ}) public

-- open SM public

-- codeSuc : ∀ {ℓ} (c : ℂ ℓ) → SZ <ₛ codeSize c
-- codeSuc C⁇ = ≤ₛ-refl
-- codeSuc C℧ = ≤ₛ-refl
-- codeSuc C𝟘 = ≤ₛ-refl
-- codeSuc C𝟙 = ≤ₛ-refl
-- codeSuc CType = ≤ₛ-refl
-- codeSuc (CΠ c cod) = ≤ₛ-sucMono ≤ₛ-Z
-- codeSuc (CΣ c cod) = ≤ₛ-sucMono ≤ₛ-Z
-- codeSuc (C≡ c x y) = ≤ₛ-sucMono ≤ₛ-Z
-- codeSuc (Cμ tyCtor c D x) = ≤ₛ-sucMono ≤ₛ-Z
-- codeSuc {ℓ = suc ℓ} (CCumul c) = (codeSuc c) ≤⨟ (≤↑ (codeSize c))

-- codeMaxL : ∀ {ℓ} (c : ℂ ℓ) → smax S1 (codeSize c) ≤ₛ codeSize c
-- codeMaxL C⁇ = smax-oneL
-- codeMaxL C℧ = smax-oneL
-- codeMaxL C𝟘 = smax-oneL
-- codeMaxL C𝟙 = smax-oneL
-- codeMaxL CType = smax-oneL
-- codeMaxL (CΠ c cod) = smax-oneL
-- codeMaxL (CΣ c cod) = smax-oneL
-- codeMaxL (C≡ c x y) = smax-oneL
-- codeMaxL (Cμ tyCtor c D x) = smax-oneL
-- codeMaxL {ℓ = suc ℓ} (CCumul c) = smax-oneL


-- codeMaxR : ∀ {ℓ} (c : ℂ ℓ) → smax (codeSize c) S1 ≤ₛ codeSize c
-- codeMaxR C⁇ = smax-oneR
-- codeMaxR C℧ = smax-oneR
-- codeMaxR C𝟘 = smax-oneR
-- codeMaxR C𝟙 = smax-oneR
-- codeMaxR CType = smax-oneR
-- codeMaxR (CΠ c cod) = smax-oneR
-- codeMaxR (CΣ c cod) = smax-oneR
-- codeMaxR (C≡ c x y) = smax-oneR
-- codeMaxR (Cμ tyCtor c D x) = smax-oneR
-- codeMaxR {ℓ = suc ℓ} (CCumul c) = smax-oneR

-- codeMaxSuc : ∀ {ℓ1 ℓ2} {c1 : ℂ ℓ1 } {c2 : ℂ ℓ2} → S1 ≤ₛ smax (codeSize c1) (codeSize c2)
-- codeMaxSuc {c1 = c1} {c2 = c2} = ≤ₛ-sucMono ≤ₛ-Z ≤⨟ smax-strictMono (codeSuc c1) (codeSuc c2)


-- ⁇suc : ∀ {{_ : Æ}} {ℓ} (x : ⁇Ty ℓ) → S1 ≤ₛ ⁇Size x
-- ⁇suc ⁇⁇ = ≤ₛ-sucMono ≤ₛ-Z
-- ⁇suc ⁇℧ = ≤ₛ-sucMono ≤ₛ-Z
-- ⁇suc ⁇𝟙 = ≤ₛ-sucMono ≤ₛ-Z
-- ⁇suc {suc ℓ} (⁇Type x) = ≤ₛ-sucMono ≤ₛ-Z
-- ⁇suc (⁇Π x) = ≤ₛ-sucMono ≤ₛ-Z
-- ⁇suc (⁇Σ x) = ≤ₛ-sucMono ≤ₛ-Z
-- ⁇suc (⁇≡ (x ⊢ .⁇⁇ ≅ .⁇⁇)) = ≤ₛ-sucMono ≤ₛ-Z
-- ⁇suc (⁇μ tyCtor x) = ≤ₛ-sucMono ≤ₛ-Z
-- ⁇suc {ℓ = suc ℓ} (⁇Cumul c x) = ≤ₛ-sucMono ≤ₛ-Z

-- open import Cubical.Data.Maybe


-- -- dataGermDescSize : {{_ : Æ}} → ℕ → CName → Size
-- -- dataGermDescSize ℓ tyCtor with numCtors tyCtor in deq
-- -- ... | ℕ.zero = S1
-- -- ... | ℕ.suc n = SLim (CFin n) λ x →
-- --     let
-- --       d : DName tyCtor
-- --       d = pSubst Fin (pSym deq) (fromCFin x)
-- --     in germDescSize (germForCtor ℓ tyCtor d) (dataGermIsCode ℓ tyCtor d) tt tt

-- -- germFCSize :  ∀ {{æ : Æ}} {ℓ} {B+ B- sig} {tyCtor : CName}
-- --       → {D : GermCtor B+ B- sig}
-- --       → {b+ : B+}
-- --       → {b- : B- b+}
-- --       → (isCode : DataGermIsCode ℓ D)
-- --       → FCGerm ℓ tyCtor D b+ b-
-- --       → Size
-- -- germFCSize {tyCtor = tyCtor} {D} {b+} {b- } isCode x = germFIndSize tyCtor D isCode b+ b- x λ r → germIndSize tyCtor (FContainer.responseNow x r)


--   -- Match on the constructor of an element of the data germ
--   -- and get back a proof that the match gives something smaller
-- -- germMatch : {{ _ : Æ }} → {ℓ : ℕ} → {tyCtor : CName}
-- --       → (dg : FContainer (germContainer ℓ tyCtor (▹⁇ ℓ))
-- --         (W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ)) (⁇Ty ℓ) tt)
-- --       → Σ[ d ∈ DName tyCtor ]
-- --         Σ[ x ∈ FCGerm ℓ tyCtor (germForCtor ℓ tyCtor d) tt tt ]
-- --         germFCSize (dataGermIsCode ℓ tyCtor d) x <ₛ germIndSize {ℓ = ℓ} tyCtor (Wsup dg)
-- -- germMatch (FC (d , com) rn ru) =
-- --     d
-- --     , FC com rn ru
-- --     , ≤ₛ-refl

-- -- dataGermInj : {{ _ : Æ }} → {ℓ : ℕ} → {tyCtor : CName} {d : DName tyCtor}
-- --       → FCGerm ℓ tyCtor (germForCtor ℓ tyCtor d) tt tt
-- --       → DataGerm ℓ tyCtor
-- -- dataGermInj {d = d} (FC com now unk) = Wsup (FC (d , com) now unk)


--   -- Used for well-founded 2-argument induction
--   -- descPairSize : ∀ {{_ : Æ}} {ℓ sig} →  {cI cB cI' cB' : ℂ ℓ} → (D1 : ℂDesc cI cB sig) (D2 : ℂDesc cI' cB' sig) → Size

--   -- codePairSize c1 c2 with codeHead c1 in eq1 | codeHead c2 in eq2 | headMatchView (codeHead c1) (codeHead c2)
--   -- ... | h1 |  h2 |  H℧L x = codeSize c2
--   -- ... | h1 |  h2 |  H℧R x = codeSize c1
--   -- ... | h1 |  h2 |  H⁇L x x₁ = codeSize c2
--   -- ... | .(HStatic _) |  h2 |  H⁇R x = codeSize c1
--   -- ... | .(HStatic _) |  .(HStatic _) |  HNeq x = smax (codeSize c1) (codeSize c2)
--   -- codePairSize (CΠ dom1 cod1) (CΠ dom2 cod2) | HStatic HΠ |  HStatic _ |  HEq reflp
--   --   = S↑ (smax (codePairSize dom1 dom2) (SLim dom1 λ x1 → SLim dom2 λ x2 → codePairSize (cod1 (approx x1)) (cod2 (approx x2))))
--   -- codePairSize (CΣ dom1 cod1) (CΣ dom2 cod2) | HStatic HΣ |  HStatic _ |  HEq reflp
--   --    = S↑ (smax (codePairSize dom1 dom2) (SLim dom1 λ x1 → SLim dom2 λ x2 → codePairSize (cod1 (approx x1)) (cod2 (approx x2))))
--   -- codePairSize (C≡ c1 x y) (C≡ c2 x₁ y₁) | HStatic H≅ |  HStatic _ |  HEq reflp
--   --   = S↑ (codePairSize c1 c2)
--   -- codePairSize C𝟙 C𝟙 | HStatic H𝟙 |  HStatic _ |  HEq reflp = S1
--   -- codePairSize C𝟘 C𝟘 | HStatic H𝟘 |  HStatic _ |  HEq reflp = S1
--   -- codePairSize CType CType | HStatic HType |  HStatic _ |  HEq reflp = S1
--   -- codePairSize (Cμ tyCtor c1 D x) (Cμ tyCtor₁ c2 D₁ x₁) | HStatic (HCtor x₂) |  HStatic _ |  HEq reflp with reflp ← eq1 with reflp ← eq2
--   --   = S↑ (DLim tyCtor λ d → descPairSize (D d) (D₁ d))


--   -- descPairSize (CEnd i) (CEnd i₁) = S1
--   -- descPairSize {cB = cB} {cB' = cB'} (CArg c D1) (CArg c' D2)
--   --   = S↑ (smax (SLim cB λ x1 → SLim cB' λ x2 → codePairSize (c (approx x1)) (c' (approx x2)) ) (descPairSize D1 D2))
--   -- descPairSize (CRec j D1) (CRec j' D2)
--   --   = S↑ (descPairSize  D1 D2)
--   -- descPairSize {cB = cB} {cB' = cB'} (CHRec c j D1) (CHRec c' j' D2)
--   --   = S↑ (smax (SLim cB λ x1 → SLim cB' λ x2 → codePairSize (c (approx x1)) (c' (approx x2)) ) (descPairSize D1 D2))


--   -- Sizes for well-formed codes
--   -- wfSize : ∀ {ℓ} → ℂwf ℓ → Size
--   -- wfSize c = codeSize (code c)

--   -- wfElSize : ∀ {{_ : Æ}} {ℓ} → (c : ℂwf ℓ) → wfEl c → Size
--   -- wfElSize c x = elSize (code c) x




--   -- wfPairSize : ∀ {ℓ} (c1 c2 : ℂwf ℓ) → Size
--   -- wfPairSize c1 c2 = csize (codePairSize (code c1) (code c2))



--   -- -- elSizeLowerBound : ∀ {ℓ} (c : ℂ ℓ) → (x : El c) → S1 ≤ₛ elSize c x
--   -- -- ⁇SizeLowerBound : ∀ {ℓ} (x : ⁇Ty ℓ) → S1 ≤ₛ ⁇Size x
--   -- -- codeSizeLowerBound : ∀ {ℓ} (c : ℂ ℓ) → S1 ≤ₛ codeSize c

--   -- -- codeSizeLowerBound C⁇ = ≤ₛ-refl
--   -- -- codeSizeLowerBound C℧ = ≤ₛ-refl
--   -- -- codeSizeLowerBound C𝟘 = ≤ₛ-refl
--   -- -- codeSizeLowerBound C𝟙 = ≤ₛ-refl
--   -- -- codeSizeLowerBound CType = ≤ₛ-refl
--   -- -- codeSizeLowerBound (CΠ c cod) = ≤ₛ-sucMono ≤ₛ-Z
--   -- -- codeSizeLowerBound (CΣ c cod) = ≤ₛ-sucMono ≤ₛ-Z
--   -- -- codeSizeLowerBound (C≡ c x y) = ≤ₛ-sucMono ≤ₛ-Z
--   -- -- codeSizeLowerBound (Cμ tyCtor c D x) with numCtors tyCtor
--   -- -- ... | ℕ.zero = ≤ₛ-refl
--   -- -- ... | ℕ.suc n = ≤ₛ-sucMono ≤ₛ-Z

--   -- -- elSizeLowerBound C⁇ x = ⁇SizeLowerBound x
--   -- -- elSizeLowerBound C℧ x = ≤ₛ-refl
--   -- -- elSizeLowerBound C𝟘 x = ≤ₛ-refl
--   -- -- elSizeLowerBound C𝟙 x = ≤ₛ-refl
--   -- -- elSizeLowerBound {suc ℓ} CType x = codeSizeLowerBound x
--   -- -- elSizeLowerBound (CΠ dom cod) f = underLim S1 (λ x → elSize (cod (approx x)) (f x)) (λ k → elSizeLowerBound (cod k) (f k))
--   -- -- elSizeLowerBound (CΣ c cod) (x , y) = ≤ₛ-trans (elSizeLowerBound c x) smax-≤L
--   -- -- elSizeLowerBound (C≡ c x₁ y) (x ⊢ _ ≅ _) = elSizeLowerBound c x
--   -- -- elSizeLowerBound (Cμ tyCtor c D x₁) (Wsup x) = ≤ₛ-sucMono ≤ₛ-Z
--   -- -- elSizeLowerBound (Cμ tyCtor c D x₁) W⁇ = ≤ₛ-sucMono ≤ₛ-Z

--   -- -- ⁇SizeLowerBound ⁇⁇ = ≤ₛ-refl
--   -- -- ⁇SizeLowerBound ⁇℧ = ≤ₛ-refl
--   -- -- ⁇SizeLowerBound ⁇𝟙 = ≤ₛ-refl
--   -- -- ⁇SizeLowerBound {suc ℓ} (⁇Type x) = codeSizeLowerBound x
--   -- -- ⁇SizeLowerBound (⁇Π x) = ≤ₛ-sucMono ≤ₛ-Z
--   -- -- ⁇SizeLowerBound (⁇Σ x) = ≤ₛ-sucMono ≤ₛ-Z
--   -- -- ⁇SizeLowerBound (⁇≡ (x ⊢ _ ≅ _)) = ≤ₛ-sucMono ≤ₛ-Z
--   -- -- ⁇SizeLowerBound (⁇μ tyCtor x) = ≤ₛ-sucMono ≤ₛ-Z

--   -- -- onePlusCode-L : ∀ {ℓ} {c1 c2 : ℂ ℓ} → codeSize c1 <o ((codeSize c1) +o (codeSize c2))
--   -- -- onePlusCode-L {c1 = c1} {c2} with (o1 , pf1) ← codeSuc c1 | (o2 , pf2) ← codeSuc c2 rewrite pf1 rewrite pf2 = ≤ₛ-sucMono (≤ₛ-trans (≤ₛ-sucMono (+o-≤-L o1 o2)) (oplus-suc-swap o1 o2))

--   -- -- onePlusCode-R : ∀ {ℓ} {c1 c2 : ℂ ℓ} → codeSize c2 <o ((codeSize c1) +o (codeSize c2))
--   -- -- onePlusCode-R {c1 = c1} {c2} with (o1 , pf1) ← codeSuc c1 | (o2 , pf2) ← codeSuc c2 rewrite pf1 rewrite pf2 = ≤ₛ-sucMono (≤ₛ-trans (≤ₛ-sucMono (+o-≤-R o1 o2)) (oplus-suc-swap o1 o2))
