
{-# OPTIONS --cubical --guarded #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Sum
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

open import Ord -- ℂ El ℧ C𝟙 refl



-- germSize {ℓ} tyCtor = wInd (λ _ → LargeOrd) (germDescFSize tyCtor (GArg (DName tyCtor) (dataGerm ℓ tyCtor (▹⁇ ℓ)))) LO1 LO1

CFin : ∀ (n : ℕ) → ℂ 0
CFin ℕ.zero = C℧
CFin (ℕ.suc n) = CΣ C𝟙 (λ { (inl false) → C℧ ; (inl true) → CFin n ; _ → C℧})


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



germFIndSize : ∀ {ℓ} (tyCtor : CName) → (D : GermDesc)
  → (DataGermIsCode ℓ D)
  → (cs : FContainer (interpGerm D) (W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ)) (⁇Ty ℓ) tt)
  → □ _ (λ _ → Ord) (tt , cs)
  → Ord
germIndSize : ∀ {ℓ} (tyCtor : CName) →  W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ) tt → Ord


germFIndSize tyCtor GEnd GEndCode (FC com k unk) φ = O1
germFIndSize tyCtor (GArg A D) (GArgCode c x₁ x₂) (FC (a , com) k unk) φ = omax O1 (germFIndSize tyCtor (D a) (x₂ a) (FC com k unk) φ )
-- germFIndSize tyCtor (GArg A D) (GArgCode c x₁ x₂) (FC (a , com) k unk)  = omax (elSize c (transport x₁ a)) (germFIndSize tyCtor (D a) (x₂ a) (FC com k unk) )
germFIndSize tyCtor (GArg A D) (GGuardedArgCode c x₁ x₂) (FC (a , com) k unk) φ =  (germFIndSize tyCtor (D a) (x₂ a) (FC com k unk) φ )
germFIndSize tyCtor (GHRec A D) (GHRecCode c x₁ x₂) (FC com k unk) φ  = O↑ (OLim c helper)
  where
   helper : El c → Ord
   helper a = omax (φ (Rec b)) (germFIndSize tyCtor (D b) (x₂ b) (FC (com b) (λ r → k (Rest (b , r))) (λ r → unk (b , r))) λ r → φ (Rest (b , r)) )
     where
       b = transport⁻ x₁ a
germFIndSize tyCtor (GHRec A D) (GGuardedHRecCode c x₁ x₂) (FC com k unk) φ = O1
germFIndSize tyCtor (GUnk A D) (GUnkCode c x pf) (FC com k unk) φ = O↑ (OLim c helper)
  where
   helper : El c → Ord
   helper a = omax O1 (germFIndSize tyCtor D pf (FC com k λ r →  unk (Rest (b , r))) φ)
     where
       b = transport⁻ x a
germFIndSize tyCtor (GUnk A D) (GGuardedUnkCode c x pf) (FC com k unk) φ = O1


--Take a tree


germIndSize {ℓ} tyCtor = wRecArg tyCtor Ord (λ d → germFIndSize tyCtor (dataGerm ℓ tyCtor (▹⁇ ℓ) d) (dataGermIsCode ℓ tyCtor d)) O1 O1

codeSize : ∀ {ℓ} → ℂ ℓ → Ord
descSize : ∀ {ℓ} →  {c : ℂ ℓ} → ℂDesc c → Ord
elSize : ∀ {ℓ} (c : ℂ ℓ) → El c → Ord
-- ▹elSize : ∀ {ℓ} (c : ℂ ℓ) → ▹El c → Ord
⁇Size : ∀ {ℓ} → ⁇Ty ℓ → Ord
LUnk : ∀ {ℓ} (æ : Æ) → LÆ {{æ}} (⁇Ty ℓ) → Ord
CμSize : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : DName tyCtor → ℂDesc cI) {i} → ℂμ tyCtor D i → Ord
CElSize : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI) (E : DName tyCtor → ℂDesc cI) {i} → ℂDescEl D (ℂμ tyCtor E) i → Ord
-- germFArgSize : ∀ {ℓ} (tyCtor : CName) → (D : GermDesc) → (DataGermIsCode ℓ D)
--   → (cs : FContainer (interpGerm D) (W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ)) (⁇Ty ℓ) tt)
--   → □ _ (λ _ → Ord) (tt , cs)
--   → Ord

-- Marks each Unk thing as having size 1, so we'll have to always handle them with normal recursion
-- germArgSize : ∀ {ℓ} (tyCtor : CName) →  W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ) tt → Ord
germDescSize : ∀ {ℓ} → (D : GermDesc)
  → (DataGermIsCode ℓ D)
  → Ord


germDescSize  GEnd GEndCode = O1
germDescSize  (GArg A D) (GArgCode c x₁ x₂) = O↑ (omax (codeSize c) (OLim c (λ a → germDescSize  (D (transport⁻ x₁ a)) (x₂ (transport⁻ x₁ a)))))
germDescSize  (GArg A D) (GGuardedArgCode c x₁ x₂) = O1
germDescSize  (GHRec A D) (GHRecCode c x₁ x₂) = O↑ (OLim c (λ a → omax (codeSize c)( germDescSize  (D (transport⁻ x₁ a)) (x₂ (transport⁻ x₁ a)))))
germDescSize  (GHRec A D) (GGuardedHRecCode c x₁ x₂) = O1
germDescSize  (GUnk A D) (GUnkCode c x pf) =  O↑ (OLim c λ a → omax (codeSize c) (germDescSize D pf))
germDescSize  (GUnk A D) (GGuardedUnkCode c x pf) = O1


-- germFArgSize tyCtor GEnd GEndCode (FC com k unk) φ = O1
-- germFArgSize tyCtor (GArg A D) (GArgCode c x₁ x₂) (FC (a , com) k unk) φ = (codeSize c)
-- germFArgSize tyCtor (GArg A D) (GGuardedArgCode c x₂ x₃) x φ = O1
-- germFArgSize tyCtor (GHRec A D) (GHRecCode c x₂ x₃) x φ = O1 -- OLim c (λ a → germFArgSize tyCtor {!!} {!!} {!!} {!!})
-- germFArgSize tyCtor (GHRec A D) (GGuardedHRecCode c x₂ x₃) x φ = O1
-- germFArgSize tyCtor (GUnk A D) (GUnkCode c x₁ pf) x φ = {!!}
-- germFArgSize tyCtor (GUnk A D) (GGuardedUnkCode c x₁ pf) x φ = O1

-- germArgSize {ℓ} tyCtor = wRecArg tyCtor Ord (λ d → germFArgSize tyCtor (dataGerm ℓ tyCtor (▹⁇ ℓ) d) (dataGermIsCode ℓ tyCtor d)) O1 O1

codeSize CodeModule.C⁇ = O1
codeSize CodeModule.C℧ = O1
codeSize CodeModule.C𝟘 = O1
codeSize CodeModule.C𝟙 = O1
codeSize CodeModule.CType = O1
codeSize (CodeModule.CΠ dom cod) = O↑ (omax (codeSize dom) (OLim dom λ x → codeSize (cod (inl x))))
codeSize (CodeModule.CΣ dom cod) = O↑ (omax (codeSize dom) ( OLim dom λ x → codeSize (cod (inl x))))
codeSize (CodeModule.C≡ c x y) = O↑ (omax (codeSize c) (omax (elSize c x) (elSize c y)) )
codeSize (CodeModule.Cμ tyCtor c D x) with numCtors tyCtor
... | ℕ.zero = O↑ OZ
... | ℕ.suc n = O↑ (OLim (CFin n) λ x → descSize (D (fromCFin x)))

descSize {c = c} (CodeModule.CEnd i) = O↑ (elSize c i )
descSize (CodeModule.CArg c D) = O↑ (OLim c (λ a → descSize (D (inl a))))
descSize {c = c} (CodeModule.CRec j D) = O↑ (omax (descSize D) (elSize c j))
descSize {c = cI} (CodeModule.CHRec c j D) = O↑ (OLim c λ a → omax (descSize (D (inl a))) (elSize cI (j a)))
-- descSize (CodeModule.CHGuard c D D₁) = O↑ (omax (descSize D) (descSize D₁))


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
⁇Size {ℓ = ℓ} (CodeModule.⁇μ tyCtor x) = ((germIndSize tyCtor x))
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
elSize (CodeModule.CΠ dom cod) f = (OLim dom λ x → elSize (cod (inl x)) (f x))
elSize (CodeModule.CΣ dom cod) (x , y) = (omax (elSize dom x) (elSize (cod (inl x)) y))
elSize (CodeModule.C≡ c x₁ y) (x ⊢ .x₁ ≅ .y) =  (elSize c x)
elSize (CodeModule.Cμ tyCtor cI D i) x = CμSize D (transport⁻ ℂμW x)



CμSize D (Cinit d x) = O↑ (CElSize (D d) D x)
CμSize D Cμ⁇ = O1
CμSize D Cμ℧ = O1

CElSize {cI = cI} .(CEnd j) E {i} (ElEnd j (w ⊢ _ ≅ _)) = elSize cI w
CElSize (CArg c D) E (ElArg a x) = O↑ (omax (elSize c a) (CElSize (D (inl a)) E x))
CElSize (CRec j D) E (ElRec x x₁) = O↑ (omax (CμSize E x) (CElSize D E x₁))
CElSize (CHRec c j D) E (ElHRec f x) = O↑ (OLim c λ a → omax (CμSize E (f a)) (CElSize (D (inl a)) E (x a)))
-- We can't use guarded arguments in size calcs, that's why they're guarded
-- So we use the size at the error value
-- CElSize (CHGuard c D1 D2) E (ElHGuard x x₁) = O↑ (omax (CElSize D1 E (x (next (℧ c)))) (CElSize D2 E x₁))







℧size : ∀ {ℓ} (c : ℂ ℓ) → elSize c (℧ c) ≤o O1
℧size CodeModule.C⁇ = ≤o-refl _
℧size CodeModule.C℧ = ≤o-refl _
℧size CodeModule.C𝟘 = ≤o-refl _
℧size CodeModule.C𝟙 = ≤o-refl _
℧size {suc ℓ} CodeModule.CType = ≤o-refl _
℧size (CodeModule.CΠ c cod) = ≤o-limiting (λ x → elSize (cod (inl x)) (℧ (CΠ c cod) x)) λ k → ℧size (cod (inl k))
℧size (CodeModule.CΣ c cod) = omax-LUB (℧size c) (℧size (cod _))
℧size (CodeModule.C≡ c x y) = ℧size c
℧size (CodeModule.Cμ tyCtor c D x) = ≤o-refl _

codeSuc : ∀ {ℓ} (c : ℂ ℓ) → OZ <o codeSize c
codeSuc CodeModule.C⁇ = ≤o-refl _
codeSuc CodeModule.C℧ = ≤o-refl _
codeSuc CodeModule.C𝟘 = ≤o-refl _
codeSuc CodeModule.C𝟙 = ≤o-refl _
codeSuc CodeModule.CType = ≤o-refl _
codeSuc (CodeModule.CΠ c cod) = ≤o-sucMono ≤o-Z
codeSuc (CodeModule.CΣ c cod) = ≤o-sucMono ≤o-Z
codeSuc (CodeModule.C≡ c x y) = ≤o-sucMono ≤o-Z
codeSuc (CodeModule.Cμ tyCtor c D x) with numCtors tyCtor
... | ℕ.zero = ≤o-refl _
... | ℕ.suc n = ≤o-sucMono ≤o-Z

codeMaxL : ∀ {ℓ} (c : ℂ ℓ) → omax O1 (codeSize c) ≤o codeSize c
codeMaxL c = omax-LUB (codeSuc c) (≤o-refl _)

codeMaxR : ∀ {ℓ} (c : ℂ ℓ) → omax (codeSize c) O1 ≤o codeSize c
codeMaxR c = omax-LUB (≤o-refl _) (codeSuc c)

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
