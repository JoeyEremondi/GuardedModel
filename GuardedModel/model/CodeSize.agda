
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
module CodeSize {{_ : DataTypes}} {{_ : DataGerms}} {{_ : DataGermCodes}} where







open import Code
-- open import Head
open import Util

open import Ord -- ℂ El ℧ C𝟙 refl



-- germSize {ℓ} tyCtor = wInd (λ _ → LargeOrd) (germDescFSize tyCtor (GArg (DName tyCtor) (dataGerm ℓ tyCtor (▹⁇ ℓ)))) LO1 LO1

CFin : ∀ (n : ℕ) → ℂ 0
CFin ℕ.zero = C℧
CFin (ℕ.suc n) = CΣ C𝟙 (λ { false → C℧ ; true → CFin n})


fromCFin : ∀ {n} → El {{æ = Approx}} (CFin n) → Fin (ℕ.suc n)
fromCFin {ℕ.zero} _ = Fin.zero
fromCFin {ℕ.suc n} (false , rest) = Fin.zero
fromCFin {ℕ.suc n} (true , rest) = Fin.suc (fromCFin rest)





germFIndSize : ∀ {{æ : Æ}} {ℓ} (tyCtor : CName) → (D : GermDesc)
  → (DataGermIsCode ℓ D)
  → (cs : FContainer (interpGerm D) (W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ)) (⁇Ty ℓ) tt)
  → □ _ (λ _ → Ord) (tt , cs)
  → Ord
germIndSize : ∀ {{ _ : Æ }} {ℓ} (tyCtor : CName) →  W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ) tt → Ord


germFIndSize tyCtor GEnd GEndCode (FC com k unk) φ = O1
germFIndSize tyCtor (GArg A D) (GArgCode c x₁ x₂) (FC (a , com) k unk) φ = omax O1 (germFIndSize tyCtor (D a) (x₂ a) (FC com k unk) φ )
-- germFIndSize tyCtor (GArg A D) (GArgCode c x₁ x₂) (FC (a , com) k unk)  = omax (elSize c (transport x₁ a)) (germFIndSize tyCtor (D a) (x₂ a) (FC com k unk) )
germFIndSize tyCtor (GArg A D) (GGuardedArgCode c x₁ x₂) (FC (a , com) k unk) φ =  (germFIndSize tyCtor (D a) (x₂ a) (FC com k unk) φ )
germFIndSize tyCtor (GHRec A D) (GHRecCode c x₁ x₂) (FC com k unk) φ  = O↑ (OLim c helper)
  where
   helper : Approxed (El c) → Ord
   helper a = omax (φ (Rec b)) (germFIndSize tyCtor (D b) (x₂ b) (FC (com b) (λ r → k (Rest (b , r))) (λ r → unk (b , r))) λ r → φ (Rest (b , r)) )
     where
       b = transport⁻ x₁ (exact a)
germFIndSize tyCtor (GHRec A D) (GGuardedHRecCode c x₁ x₂) (FC com k unk) φ = O1
germFIndSize tyCtor (GUnk A D) (GUnkCode c x pf) (FC com k unk) φ = O↑ (OLim c helper)
  where
   helper : Approxed (El c) → Ord
   helper a = omax O1 (germFIndSize tyCtor D pf (FC com k λ r →  unk (Rest (b , r))) φ)
     where
       b = transport⁻ x (exact a)
germFIndSize tyCtor (GUnk A D) (GGuardedUnkCode c x pf) (FC com k unk) φ = O1




germIndSize {ℓ} tyCtor = wRecArg tyCtor Ord (λ d → germFIndSize tyCtor (dataGerm ℓ tyCtor (▹⁇ ℓ) d) (dataGermIsCode ℓ tyCtor d)) O1 O1

codeSize : ∀ {ℓ} → ℂ ℓ → Ord
descSize : ∀  {ℓ} →  {c : ℂ ℓ} → ℂDesc c → Ord
elSize : ∀ {{_ : Æ}} {ℓ} (c : ℂ ℓ) → El c → Ord
-- ▹elSize : ∀ {ℓ} (c : ℂ ℓ) → ▹El c → Ord
⁇Size : ∀ {{ _ : Æ}} {ℓ} → ⁇Ty ℓ → Ord
CμSize : ∀ {{_ : Æ}} {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : DName tyCtor → ℂDesc cI) {i} → ℂμ tyCtor D i → Ord
CElSize : ∀ {{ _ : Æ }} {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI) (E : DName tyCtor → ℂDesc cI) {i} → ℂDescEl D (ℂμ tyCtor E) i → Ord
-- germFArgSize : ∀ {ℓ} (tyCtor : CName) → (D : GermDesc) → (DataGermIsCode ℓ D)
--   → (cs : FContainer (interpGerm D) (W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ)) (⁇Ty ℓ) tt)
--   → □ _ (λ _ → Ord) (tt , cs)
--   → Ord

-- Marks each Unk thing as having size 1, so we'll have to always handle them with normal recursion
-- germArgSize : ∀ {ℓ} (tyCtor : CName) →  W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ) tt → Ord
germDescSize : ∀ {{_ : Æ}} {ℓ} → (D : GermDesc)
  → (DataGermIsCode ℓ D)
  → Ord


germDescSize  GEnd GEndCode = O1
germDescSize  (GArg A D) (GArgCode c x₁ x₂) = O↑ (omax (codeSize c) (OLim c (λ a → germDescSize  (D (transport⁻ x₁ (exact a))) (x₂ (transport⁻ x₁ (exact a))))))
germDescSize  (GArg A D) (GGuardedArgCode c x₁ x₂) = O1
germDescSize  (GHRec A D) (GHRecCode c x₁ x₂) = O↑ (OLim c (λ a → omax (codeSize c)( germDescSize  (D (transport⁻ x₁ (exact a))) (x₂ (transport⁻ x₁ (exact a))))))
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

codeSize C⁇ = O1
codeSize C℧ = O1
codeSize C𝟘 = O1
codeSize C𝟙 = O1
codeSize CType = O1
codeSize (CΠ dom cod) = O↑ (omax (codeSize dom) (OLim {{æ = Approx}} dom λ x → codeSize (cod x)))
codeSize (CΣ dom cod) = O↑ (omax (codeSize dom) ( OLim  {{æ = Approx}} dom λ x → codeSize (cod x)))
codeSize  (C≡ c x y) = O↑ (omax (codeSize c) (omax (elSize {{Approx}} c x) (elSize {{Approx}}  c y)) )
codeSize (Cμ tyCtor c D x) with numCtors tyCtor
... | ℕ.zero = O↑ OZ
... | ℕ.suc n = O↑ (OLim {{æ = Approx}} (CFin n) λ x → descSize (D (fromCFin x)))

descSize {c = c} (CEnd i) = O↑ (elSize {{Approx}} c i )
descSize (CArg c D) = O↑ (OLim {{æ = Approx}} c (λ a → descSize (D a)))
descSize {c = c} (CRec j D) = O↑ (omax (descSize D) (elSize {{Approx}} c j))
descSize {c = cI} (CHRec c j D) = O↑ (OLim {{æ = Approx}} c λ a → omax (descSize (D a)) (elSize {{Approx}} cI (j a)))
-- descSize (CHGuard c D D₁) = O↑ (omax (descSize D) (descSize D₁))


-- There are no codes of size zero
noCodeZero : ∀ {ℓ} (c : ℂ ℓ) → ¬ (codeSize c ≡p OZ)
noCodeZero (Cμ tyCtor c D x) eq with numCtors tyCtor
noCodeZero (Cμ tyCtor c D x) () | ℕ.zero
noCodeZero (Cμ tyCtor c D x) () | ℕ.suc n


-- argLessLeft : ∀ o1 o2 → o1 <o O↑ (omax o1 o2)
-- argLessLeft o1 o2 = ≤o-sucMono omax-≤L

-- argLessRight : ∀ o1 o2 → o2 <o O↑ (omax o1 o2)
-- argLessRight o1 o2 = ≤o-sucMono omax-≤R







⁇Size ⁇⁇ = O1
⁇Size ⁇℧ = O1
⁇Size ⁇𝟙 = O1
⁇Size {ℓ = ℕ.suc ℓ} (⁇Type x) = O↑  (codeSize x)
⁇Size (⁇Π f) = O↑ (OLim C⁇ (λ x → ⁇Size (f (transport (sym hollowEq) (next (exact x)))))) -- O↑ (OLim C⁇ (λ x → LUnk æ ))
⁇Size (⁇Σ (x , y)) = O↑ (omax (⁇Size x) (⁇Size y))
⁇Size (⁇≡ (x ⊢ .⁇⁇ ≅ .⁇⁇)) = O↑ (⁇Size x)
⁇Size {ℓ = ℓ} (⁇μ tyCtor x) = ((germIndSize tyCtor x))
-- O1 --TODO does this cause problems?
-- CμSize (dataGermCode ℓ tyCtor) (transport⁻ (dataGermCodeEq ℓ tyCtor) x)
  -- where
  --   cx : ℂμ1 tyCtor (dataGermCode ℓ tyCtor) true
  --   cx =  transport⁻ (dataGermCodeEq ℓ tyCtor) x


elSize C⁇ x = ⁇Size x
elSize C℧ x = O1
elSize C𝟘 x = O1
elSize C𝟙 x = O1
elSize {suc ℓ} CType x = (codeSize x)
elSize (CΠ dom cod) f = OLim dom (λ x → elSize (cod (approx x)) (f x)) -- (OLim dom λ x → elSize (cod (approx x)) (f ?))
elSize (CΣ dom cod) (x , y) = (omax (elSize dom (exact x)) (elSize (cod (approx x)) y))
elSize (C≡ c x₁ y) (x ⊢ .x₁ ≅ .y) = (elSize {{Approx}} c x)
elSize (Cμ tyCtor cI D i) x = CμSize D (transport⁻ ℂμW x)



CμSize D (Cinit d x) = O↑ (CElSize (D d) D x)
CμSize D Cμ⁇ = O1
CμSize D Cμ℧ = O1

CElSize {cI = cI} .(CEnd j) E {i} (ElEnd j (w ⊢ _ ≅ _)) = elSize {{Approx}} cI w
CElSize {{æ}} (CArg c D) E (ElArg a x) = O↑ (omax (elSize {{æ}} c (exact a)) (CElSize (D (approx a)) E x))
CElSize (CRec j D) E (ElRec x x₁) = O↑ (omax (CμSize E x) (CElSize D E x₁))
CElSize (CHRec c j D) E (ElHRec f x) = O↑ (OLim c λ a → omax (CμSize E (f a)) (CElSize (D (approx a)) E (x a)))
-- We can't use guarded arguments in size calcs, that's why they're guarded
-- So we use the size at the error value
-- CElSize (CHGuard c D1 D2) E (ElHGuard x x₁) = O↑ (omax (CElSize D1 E (x (next (℧ c)))) (CElSize D2 E x₁))







℧size : ∀ {{_ : Æ}} {ℓ} (c : ℂ ℓ) → elSize c (℧ c) ≤o O1
℧size C⁇ = ≤o-refl _
℧size C℧ = ≤o-refl _
℧size C𝟘 = ≤o-refl _
℧size C𝟙 = ≤o-refl _
℧size {suc ℓ} CType = ≤o-refl _
℧size (CΠ c cod) = ≤o-limiting (λ x → elSize (cod (approx x)) (℧ (CΠ c cod) x)) λ k → ℧size (cod (approx k))
℧size ⦃ Approx ⦄ (CodeModule.CΣ c cod) = omax-LUB (℧size {{Approx}} c ) (℧size ⦃ Approx ⦄ (cod (℧ c {{Approx}})))
℧size ⦃ Exact ⦄ (CodeModule.CΣ c cod) = omax-LUB (℧size {{Exact}} c ) (℧size ⦃ Exact ⦄ (cod (℧ c {{Approx}})))
℧size (C≡ c x y) = ℧size {{Approx}} c
℧size (Cμ tyCtor c D x) = ≤o-refl _

codeSuc : ∀ {ℓ} (c : ℂ ℓ) → OZ <o codeSize c
codeSuc C⁇ = ≤o-refl _
codeSuc C℧ = ≤o-refl _
codeSuc C𝟘 = ≤o-refl _
codeSuc C𝟙 = ≤o-refl _
codeSuc CType = ≤o-refl _
codeSuc (CΠ c cod) = ≤o-sucMono ≤o-Z
codeSuc (CΣ c cod) = ≤o-sucMono ≤o-Z
codeSuc (C≡ c x y) = ≤o-sucMono ≤o-Z
codeSuc (Cμ tyCtor c D x) with numCtors tyCtor
... | ℕ.zero = ≤o-refl _
... | ℕ.suc n = ≤o-sucMono ≤o-Z

codeMaxL : ∀ {ℓ} (c : ℂ ℓ) → omax O1 (codeSize c) ≤o codeSize c
codeMaxL c = omax-LUB (codeSuc c) (≤o-refl _)

codeMaxR : ∀ {ℓ} (c : ℂ ℓ) → omax (codeSize c) O1 ≤o codeSize c
codeMaxR c = omax-LUB (≤o-refl _) (codeSuc c)

open import Cubical.Data.Maybe


dataGermDescSize : {{_ : Æ}} → ℕ → CName → Ord
dataGermDescSize ℓ tyCtor with numCtors tyCtor in deq
... | ℕ.zero = O1
... | ℕ.suc n = OLim {{æ = Approx}} (CFin n) λ x →
  let
    d : DName tyCtor
    d = pSubst Fin (pSym deq) (fromCFin x)
  in germDescSize (dataGerm ℓ tyCtor (▹⁇ ℓ) d) (dataGermIsCode ℓ tyCtor d)


checkCtorSmaller :
     {{_ : Æ}}
     → (ℓ : ℕ)
     → (tyCtor : CName)
     → (cI : ℂ ℓ)
     → (D : ℂDesc cI )
     → (GD : GermDesc)
     → (pf : DataGermIsCode ℓ GD)
     → (d : DName tyCtor)
     → Maybe (germDescSize GD pf ≤o descSize D)
checkCtorSmaller ℓ tyCtor cI D d = {!!}

checkDataGermSmaller :
     {{_ : Æ}}
     → (ℓ : ℕ)
     → (tyCtor : CName)
     → (cI : ℂ ℓ)
     → (D : DName tyCtor → ℂDesc cI )
     → (i : ApproxEl cI)
     → Maybe (dataGermDescSize ℓ tyCtor ≤o codeSize (Cμ tyCtor cI D i))
checkDataGermSmaller ℓ tyCtor cI D i = {!!}




-- codeSuc : ∀ {ℓ} (c : ℂ ℓ) → Σ[ o ∈ Ord ](codeSize c ≡p O↑ o)
-- codeSuc C⁇ = _ , reflp
-- codeSuc C℧ = _ , reflp
-- codeSuc C𝟘 = _ , reflp
-- codeSuc C𝟙 = _ , reflp
-- codeSuc CType = _ , reflp
-- codeSuc (CΠ c cod) = _ , reflp
-- codeSuc (CΣ c cod) = _ , reflp
-- codeSuc (C≡ c x y) = _ , reflp
-- codeSuc (Cμ tyCtor c D x) with numCtors tyCtor
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
-- -- elSizeLowerBound (CΠ dom cod) f = underLim O1 (λ x → elSize (cod (approx x)) (f x)) (λ k → elSizeLowerBound (cod k) (f k))
-- -- elSizeLowerBound (CΣ c cod) (x , y) = ≤o-trans (elSizeLowerBound c x) omax-≤L
-- -- elSizeLowerBound (C≡ c x₁ y) (x ⊢ _ ≅ _) = elSizeLowerBound c x
-- -- elSizeLowerBound (Cμ tyCtor c D x₁) (Wsup x) = ≤o-sucMono ≤o-Z
-- -- elSizeLowerBound (Cμ tyCtor c D x₁) W℧ = ≤o-sucMono ≤o-Z
-- -- elSizeLowerBound (Cμ tyCtor c D x₁) W⁇ = ≤o-sucMono ≤o-Z

-- -- ⁇SizeLowerBound ⁇⁇ = ≤o-refl _
-- -- ⁇SizeLowerBound ⁇℧ = ≤o-refl _
-- -- ⁇SizeLowerBound ⁇𝟙 = ≤o-refl _
-- -- ⁇SizeLowerBound {suc ℓ} (⁇Type x) = codeSizeLowerBound x
-- -- ⁇SizeLowerBound (⁇Π x) = ≤o-sucMono ≤o-Z
-- -- ⁇SizeLowerBound (⁇Σ x) = ≤o-sucMono ≤o-Z
-- -- ⁇SizeLowerBound (⁇≡ (x ⊢ _ ≅ _)) = ≤o-sucMono ≤o-Z
-- -- ⁇SizeLowerBound (⁇μ tyCtor x) = ≤o-sucMono ≤o-Z

-- onePlusCode-L : ∀ {ℓ} {c1 c2 : ℂ ℓ} → codeSize c1 <o ((codeSize c1) +o (codeSize c2))
-- onePlusCode-L {c1 = c1} {c2} with (o1 , pf1) ← codeSuc c1 | (o2 , pf2) ← codeSuc c2 rewrite pf1 rewrite pf2 = ≤o-sucMono (≤o-trans (≤o-sucMono (+o-≤-L o1 o2)) (oplus-suc-swap o1 o2))

-- onePlusCode-R : ∀ {ℓ} {c1 c2 : ℂ ℓ} → codeSize c2 <o ((codeSize c1) +o (codeSize c2))
-- onePlusCode-R {c1 = c1} {c2} with (o1 , pf1) ← codeSuc c1 | (o2 , pf2) ← codeSuc c2 rewrite pf1 rewrite pf2 = ≤o-sucMono (≤o-trans (≤o-sucMono (+o-≤-R o1 o2)) (oplus-suc-swap o1 o2))
