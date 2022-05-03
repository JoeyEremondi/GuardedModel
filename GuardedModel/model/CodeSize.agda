
{-# OPTIONS --cubical --guarded #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Equality
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Inductives
open import GuardedAlgebra
open import Cubical.Induction.WellFounded
open import Cubical.Foundations.Prelude
open import Cubical.Data.Equality using (ptoc)

open import ApproxExact

open import InductiveCodes
open import Cubical.Foundations.Transport

open import DataGerm

-- Brouwer Tree ordinals
-- Based on the presentation by Kraus, Forsburg and Xu
-- https://arxiv.org/abs/2104.02549

-- The main difference is that we allow the limit over the elements of any code type, not just natural numbers

--TODO: don't make ℓ module param
module CodeSize {{æ : Æ}} {{_ : Datatypes}} {{_ : DataGermCodes}} where







open import Code
-- open import Head
open import Util

open import Ord ℂ El ℧ C𝟙 refl
-- Marks each Unk thing as having size 1, so we'll have to always handle them with normal recursion
germSize : ∀ {ℓ} (tyCtor : CName) → W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ) tt → LargeOrd
germDescFSize : ∀ {ℓ} (tyCtor : CName) → (D : GermDesc)
  → (cs : FContainer (interpGerm D) (W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ)) (⁇Ty ℓ) tt)
  → □ _ (λ _ → LargeOrd) (tt , cs)
  → LargeOrd
germDescFSize tyCtor D (FC com k unk) φ = {!D!}

germSize {ℓ} tyCtor = wInd (λ _ → LargeOrd) (germDescFSize tyCtor (GArg (DName tyCtor) (dataGerm ℓ tyCtor (▹⁇ ℓ)))) LO1 LO1

CFin : ∀ (n : ℕ) → ℂ 0
CFin ℕ.zero = C℧
CFin (ℕ.suc n) = CΣ C𝟙 (λ { false → C℧ ; true → CFin n})


fromCFin : ∀ {n} → El (CFin n) → Fin (ℕ.suc n)
fromCFin {ℕ.zero} x = Fin.zero
fromCFin {ℕ.suc n} (false , rest) = Fin.zero
fromCFin {ℕ.suc n} (true , rest) = Fin.suc (fromCFin rest)





-- GermSize : ∀ {ℓ} (tyCtor : CName) {i} → ℂμ tyCtor (dataGermCode ℓ tyCtor) i → Ord
-- TreeSize : ∀ {ℓ} {tyCtor : CName} (D : ℂDesc {ℓ} C𝟙) {i} → ℂDescEl D (ℂμ tyCtor (dataGermCode ℓ tyCtor)) i → Ord
-- GermSize {ℓ} tyCtor (Cinit d x) = O↑ (TreeSize (dataGermCode ℓ tyCtor d) x)
-- GermSize tyCtor Cμ⁇ = O1
-- GermSize tyCtor Cμ℧ = O1

-- TreeSize .(CEnd j) {i} (ElEnd j (w ⊢ _ ≅ _)) = O1
-- TreeSize (CArg c D) (ElArg a x) = O↑ ( (TreeSize (D a) x))
-- TreeSize (CRec j D) (ElRec x x₁) = O↑ (omax (GermSize _ x) (TreeSize D x₁))
-- TreeSize (CHRec c j D) (ElHRec f x) = O↑ (OLim c λ a → omax (GermSize _ (f a)) (TreeSize (D a) (x a)))
-- -- We can't use guarded arguments in size calcs, that's why they're guarded
-- -- So we use the size at the error value
-- TreeSize (CHGuard c D1 D2) (ElHGuard x x₁) = O↑ (omax (TreeSize D1 (x (next (℧ c)))) (TreeSize D2 x₁))


codeSize : ∀ {ℓ} → ℂ ℓ → Ord
descSize : ∀ {ℓ} →  {c : ℂ ℓ} → ℂDesc c → Ord
elSize : ∀ {ℓ} (c : ℂ ℓ) → El c → Ord
⁇Size : ∀ {ℓ} → ⁇Ty ℓ → Ord
LUnk : ∀ {ℓ} (æ : Æ) → LÆ {{æ}} (⁇Ty ℓ) → Ord
CμSize : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : DName tyCtor → ℂDesc cI) {i} → ℂμ tyCtor D i → Ord
CElSize : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI) (E : DName tyCtor → ℂDesc cI) {i} → ℂDescEl D (ℂμ tyCtor E) i → Ord


-- GermSizeW : ∀ {ℓ} (tyCtor : CName)  → W (germContainer ℓ tyCtor (dfix F⁇)) (⁇Ty ℓ) tt → Ord
-- TreeSizeW : ∀ {ℓ} (tyCtor : CName)
--   → (D : GermDesc)
--   → FContainer (interpGerm D) (W (germContainer ℓ tyCtor (dfix F⁇)) (⁇Ty ℓ)) (⁇Ty ℓ) tt
--   → DataGermIsCode ℓ D
--   → Ord
-- TreeSizeW tyCtor GEnd (FC com k unk) GEndCode = {!!}
-- TreeSizeW tyCtor (GArg A x) (FC (a , com) k unk) (GArgCode c x₁ x₂) = O↑ (omax (codeSize c) {!!})
-- TreeSizeW tyCtor (GArg .(∀ x₄ → _ x₄) x) (FC com k unk) (GGuardedArgCode ca x₁ x₂ x₃) = {!!}
-- TreeSizeW tyCtor (GHRec A x) (FC com k unk) (GHRecCode c x₁ x₂) = {!!}
-- TreeSizeW tyCtor (GHRec A x) (FC com k unk) (GGuardedRecCode c x₁ x₂) = {!!}
-- TreeSizeW tyCtor (GUnk A D) (FC com k unk) (GUnkCode c x pf) = {!!}
-- TreeSizeW tyCtor (GUnk A D) (FC com k unk) (GGuardedUnkCode c x pf) = {!!}

-- GermSizeW {ℓ} tyCtor (Wsup (FC (d , c) k unk))
--   = O↑ (TreeSizeW tyCtor (dataGerm ℓ tyCtor (dfix F⁇) d) (FC c k unk) (dataGermIsCode ℓ tyCtor d))
-- GermSizeW tyCtor W℧ = O1
-- GermSizeW tyCtor W⁇ = O1

codeSize CodeModule.C⁇ = O1
codeSize CodeModule.C℧ = O1
codeSize CodeModule.C𝟘 = O1
codeSize CodeModule.C𝟙 = O1
codeSize CodeModule.CType = O1
codeSize (CodeModule.CΠ dom cod) = O↑ (omax (codeSize dom) (OLim dom λ x → codeSize (cod x)))
codeSize (CodeModule.CΣ dom cod) = O↑ (omax (codeSize dom) ( OLim dom λ x → codeSize (cod x)))
codeSize (CodeModule.C≡ c x y) = O↑ (omax (codeSize c) (omax (elSize c x) (elSize c y)) )
codeSize (CodeModule.Cμ tyCtor c D x) with numCtors tyCtor
... | ℕ.zero = O↑ OZ
... | ℕ.suc n = O↑ (OLim (CFin n) λ x → descSize (D (fromCFin x)))

descSize {c = c} (CodeModule.CEnd i) = O↑ (elSize c i )
descSize (CodeModule.CArg c D) = O↑ (OLim c (λ a → descSize (D a)))
descSize {c = c} (CodeModule.CRec j D) = O↑ (omax (descSize D) (elSize c j))
descSize {c = cI} (CodeModule.CHRec c j D) = O↑ (OLim c λ a → omax (descSize (D a)) (elSize cI (j a)))
descSize (CodeModule.CHGuard c D D₁) = O↑ (omax (descSize D) (descSize D₁))


-- There are no codes of size zero
noCodeZero : ∀ {ℓ} (c : ℂ ℓ) → ¬ (codeSize c ≡p OZ)
noCodeZero (CodeModule.Cμ tyCtor c D x) eq with numCtors tyCtor
noCodeZero (CodeModule.Cμ tyCtor c D x) () | ℕ.zero
noCodeZero (CodeModule.Cμ tyCtor c D x) () | ℕ.suc n


-- argLessLeft : ∀ o1 o2 → o1 <o O↑ (omax o1 o2)
-- argLessLeft o1 o2 = ≤o-sucMono omax-≤L

-- argLessRight : ∀ o1 o2 → o2 <o O↑ (omax o1 o2)
-- argLessRight o1 o2 = ≤o-sucMono omax-≤R







⁇Size CodeModule.⁇⁇ = O1
⁇Size CodeModule.⁇℧ = O1
⁇Size CodeModule.⁇𝟙 = O1
⁇Size {ℓ = ℕ.suc ℓ} (CodeModule.⁇Type x) = O↑  (codeSize x)
⁇Size (CodeModule.⁇Π f) = O↑ (OLim C⁇ (λ x → ⁇Size (f (transport (sym hollowEq) (next x))))) -- O↑ (OLim C⁇ (λ x → LUnk æ ))
⁇Size (CodeModule.⁇Σ (x , y)) = O↑ (omax (⁇Size x) (⁇Size y))
⁇Size (CodeModule.⁇≡ (x ⊢ .⁇⁇ ≅ .⁇⁇)) = O↑ (⁇Size x)
⁇Size {ℓ = ℓ} (CodeModule.⁇μ tyCtor x) = {!!} -- dataGermSize tyCtor x
-- O1 --TODO does this cause problems?
-- CμSize (dataGermCode ℓ tyCtor) (transport⁻ (dataGermCodeEq ℓ tyCtor) x)
  -- where
  --   cx : ℂμ1 tyCtor (dataGermCode ℓ tyCtor) true
  --   cx =  transport⁻ (dataGermCodeEq ℓ tyCtor) x
LUnk Approx (Now x) = O↑ (⁇Size x)
LUnk Exact x = O1


elSize CodeModule.C⁇ x = ⁇Size x
elSize CodeModule.C℧ x = O1
elSize CodeModule.C𝟘 x = O1
elSize CodeModule.C𝟙 x = O1
elSize {suc ℓ} CodeModule.CType x = (codeSize x)
elSize (CodeModule.CΠ dom cod) f = (OLim dom λ x → elSize (cod x) (f x))
elSize (CodeModule.CΣ dom cod) (x , y) = (omax (elSize dom x) (elSize (cod x) y))
elSize (CodeModule.C≡ c x₁ y) (x ⊢ .x₁ ≅ .y) =  (elSize c x)
elSize (CodeModule.Cμ tyCtor cI D i) x = CμSize D (transport⁻ ℂμW x)



CμSize D (Cinit d x) = O↑ (CElSize (D d) D x)
CμSize D Cμ⁇ = O1
CμSize D Cμ℧ = O1

CElSize {cI = cI} .(CEnd j) E {i} (ElEnd j (w ⊢ _ ≅ _)) = elSize cI w
CElSize (CArg c D) E (ElArg a x) = O↑ (omax (elSize c a) (CElSize (D a) E x))
CElSize (CRec j D) E (ElRec x x₁) = O↑ (omax (CμSize E x) (CElSize D E x₁))
CElSize (CHRec c j D) E (ElHRec f x) = O↑ (OLim c λ a → omax (CμSize E (f a)) (CElSize (D a) E (x a)))
-- We can't use guarded arguments in size calcs, that's why they're guarded
-- So we use the size at the error value
CElSize (CHGuard c D1 D2) E (ElHGuard x x₁) = O↑ (omax (CElSize D1 E (x (next (℧ c)))) (CElSize D2 E x₁))


-- ℧size : ∀ {ℓ} (c : ℂ ℓ) → elSize c (℧ c) ≤o O1
-- ℧size CodeModule.C⁇ = ≤o-refl _
-- ℧size CodeModule.C℧ = ≤o-refl _
-- ℧size CodeModule.C𝟘 = ≤o-refl _
-- ℧size CodeModule.C𝟙 = ≤o-refl _
-- ℧size {suc ℓ} CodeModule.CType = ≤o-refl _
-- ℧size (CodeModule.CΠ c cod) = ≤o-limiting (λ x → elSize (cod x) (℧ (CΠ c cod) x)) (λ k → ℧size (cod k))
-- ℧size (CodeModule.CΣ c cod) = omax-LUB (℧size c) (℧size (cod _))
-- ℧size (CodeModule.C≡ c x y) = ℧size c
-- ℧size (CodeModule.Cμ tyCtor c D x) = ≤o-refl _

-- codeSuc : ∀ {ℓ} (c : ℂ ℓ) → Σ[ o ∈ Ord ](codeSize c ≡p O↑ o)
-- codeSuc CodeModule.C⁇ = _ , reflp
-- codeSuc CodeModule.C℧ = _ , reflp
-- codeSuc CodeModule.C𝟘 = _ , reflp
-- codeSuc CodeModule.C𝟙 = _ , reflp
-- codeSuc CodeModule.CType = _ , reflp
-- codeSuc (CodeModule.CΠ c cod) = _ , reflp
-- codeSuc (CodeModule.CΣ c cod) = _ , reflp
-- codeSuc (CodeModule.C≡ c x y) = _ , reflp
-- codeSuc (CodeModule.Cμ tyCtor c D x) with numCtors tyCtor
-- ... | ℕ.zero = _ , reflp
-- ... | ℕ.suc n = _ , reflp

-- -- elSizeLowerBound : ∀ {ℓ} (c : ℂ ℓ) → (x : El c) → O1 ≤o elSize c x
-- -- ⁇SizeLowerBound : ∀ {ℓ} (x : ⁇Ty ℓ) → O1 ≤o ⁇Size x
-- -- codeSizeLowerBound : ∀ {ℓ} (c : ℂ ℓ) → O1 ≤o codeSize c

-- -- codeSizeLowerBound C⁇ = ≤o-refl _
-- -- codeSizeLowerBound C℧ = ≤o-refl _
-- -- codeSizeLowerBound C𝟘 = ≤o-refl _
-- -- codeSizeLowerBound C𝟙 = ≤o-refl _
-- -- codeSizeLowerBound CType = ≤o-refl _
-- -- codeSizeLowerBound (CΠ c cod) = ≤o-sucMono ≤o-Z
-- -- codeSizeLowerBound (CΣ c cod) = ≤o-sucMono ≤o-Z
-- -- codeSizeLowerBound (C≡ c x y) = ≤o-sucMono ≤o-Z
-- -- codeSizeLowerBound (Cμ tyCtor c D x) with numCtors tyCtor
-- -- ... | ℕ.zero = ≤o-refl _
-- -- ... | ℕ.suc n = ≤o-sucMono ≤o-Z

-- -- elSizeLowerBound C⁇ x = ⁇SizeLowerBound x
-- -- elSizeLowerBound C℧ x = ≤o-refl _
-- -- elSizeLowerBound C𝟘 x = ≤o-refl _
-- -- elSizeLowerBound C𝟙 x = ≤o-refl _
-- -- elSizeLowerBound {suc ℓ} CType x = codeSizeLowerBound x
-- -- elSizeLowerBound (CΠ dom cod) f = underLim O1 (λ x → elSize (cod x) (f x)) (λ k → elSizeLowerBound (cod k) (f k))
-- -- elSizeLowerBound (CΣ c cod) (x , y) = ≤o-trans (elSizeLowerBound c x) omax-≤L
-- -- elSizeLowerBound (C≡ c x₁ y) (x ⊢ _ ≅ _) = elSizeLowerBound c x
-- -- elSizeLowerBound (CodeModule.Cμ tyCtor c D x₁) (Wsup x) = ≤o-sucMono ≤o-Z
-- -- elSizeLowerBound (CodeModule.Cμ tyCtor c D x₁) W℧ = ≤o-sucMono ≤o-Z
-- -- elSizeLowerBound (CodeModule.Cμ tyCtor c D x₁) W⁇ = ≤o-sucMono ≤o-Z

-- -- ⁇SizeLowerBound CodeModule.⁇⁇ = ≤o-refl _
-- -- ⁇SizeLowerBound CodeModule.⁇℧ = ≤o-refl _
-- -- ⁇SizeLowerBound CodeModule.⁇𝟙 = ≤o-refl _
-- -- ⁇SizeLowerBound {suc ℓ} (CodeModule.⁇Type x) = codeSizeLowerBound x
-- -- ⁇SizeLowerBound (CodeModule.⁇Π x) = ≤o-sucMono ≤o-Z
-- -- ⁇SizeLowerBound (CodeModule.⁇Σ x) = ≤o-sucMono ≤o-Z
-- -- ⁇SizeLowerBound (CodeModule.⁇≡ (x ⊢ _ ≅ _)) = ≤o-sucMono ≤o-Z
-- -- ⁇SizeLowerBound (CodeModule.⁇μ tyCtor x) = ≤o-sucMono ≤o-Z

-- onePlusCode-L : ∀ {ℓ} {c1 c2 : ℂ ℓ} → codeSize c1 <o ((codeSize c1) +o (codeSize c2))
-- onePlusCode-L {c1 = c1} {c2} with (o1 , pf1) ← codeSuc c1 | (o2 , pf2) ← codeSuc c2 rewrite pf1 rewrite pf2 = ≤o-sucMono (≤o-trans (≤o-sucMono (+o-≤-L o1 o2)) (oplus-suc-swap o1 o2))

-- onePlusCode-R : ∀ {ℓ} {c1 c2 : ℂ ℓ} → codeSize c2 <o ((codeSize c1) +o (codeSize c2))
-- onePlusCode-R {c1 = c1} {c2} with (o1 , pf1) ← codeSuc c1 | (o2 , pf2) ← codeSuc c2 rewrite pf1 rewrite pf2 = ≤o-sucMono (≤o-trans (≤o-sucMono (+o-≤-R o1 o2)) (oplus-suc-swap o1 o2))
