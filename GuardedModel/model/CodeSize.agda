

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
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Equality using (ptoc)

open import ApproxExact

-- open import InductiveCodes
open import Cubical.Foundations.Transport


-- Brouwer Tree ordinals
-- Based on the presentation by Kraus, Forsburg and Xu
-- https://arxiv.org/abs/2104.02549

-- The main difference is that we allow the limit over the elements of any code type, not just natural numbers

open import InductiveCodes
module CodeSize {{_ : DataTypes}} {{_ : DataGerms}} {{_ : InductiveCodes }} where







open import Code
open import WMuEq
open import Head
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


toCFin : ∀ {n} → Fin (ℕ.suc n) → El {{æ = Approx}} (CFin n)
toCFin {n = ℕ.zero} x = tt
toCFin {n = ℕ.suc n} Fin.zero = false , tt
toCFin {n = ℕ.suc n} (Fin.suc x) = true , toCFin x

fromToCFin : ∀ {n} (x : Fin (ℕ.suc n)) → fromCFin (toCFin x) ≡p x
fromToCFin {ℕ.zero} Fin.zero = reflp
fromToCFin {ℕ.suc n} Fin.zero = reflp
fromToCFin {ℕ.suc n} (Fin.suc x) rewrite fromToCFin x = reflp


germFIndSize : ∀ {{æ : Æ}} {ℓ} {B} (tyCtor : CName) → (D : GermCtor B)
  → (DataGermIsCode ℓ D)
  → (b : B)
  → (cs : FContainer (interpGermCtor D b) (W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ)) (⁇Ty ℓ) tt)
  → □ _ (λ _ → Ord) (tt , cs)
  → Ord
germIndSize : ∀ {{ _ : Æ }} {ℓ} (tyCtor : CName) →  W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ) tt → Ord


germFIndSize tyCtor GEnd GEndCode b (FC com k unk) φ = O1
germFIndSize tyCtor (GRec D) (GRecCode c pf) b (FC com k unk) φ =
  O↑ (omax (φ (Rec tt)) (germFIndSize tyCtor D pf b (FC com (λ r → k (Rest r)) unk) (λ r → φ (Rest r))))
germFIndSize tyCtor (GArg A D) (GArgCode c isom pf) b (FC (a , com) k unk) φ = O↑ (germFIndSize tyCtor D pf (b , a) (FC com k unk) φ)
germFIndSize tyCtor (GArg A D) (GGuardedArgCode c x pf) b (FC com k unk) φ = O1
germFIndSize {{æ}} tyCtor (GHRec A D) (GHRecCode c isom pf) b (FC com k unk) φ = O↑ (OLim (c b) helper)
  where
    helper : Approxed (λ {{æ}} → El {{æ = æ}} (c b))  → Ord
    helper a = omax (φ (Rec ac)) (germFIndSize tyCtor D pf b (FC com (λ r → k (Rest (ac , r))) unk) λ r → φ (Rest (ac , r)))
      where
        ac : A b
        ac = Iso.inv (isom b) (exact a)
germFIndSize tyCtor (GHRec A D) (GGuardedHRecCode c x pf) b (FC com k unk) φ = O1
germFIndSize tyCtor (GUnk A D) (GUnkCode c isom pf) b (FC com k unk) φ = O↑ (OLim (c b) helper)
  where
    helper : Approxed (λ {{æ}} → El {{æ = æ}} (c b))  → Ord
    helper a =  germFIndSize tyCtor D pf b (FC com k λ r → unk (Rest ((ac , r)))) φ
      where
        ac : A b
        ac = Iso.inv (isom b) (exact a)
germFIndSize tyCtor (GUnk A D) (GGuardedUnkCode c x pf) b (FC com k unk) φ = O1


germIndSize {ℓ} tyCtor = wRecArg tyCtor Ord (λ d → germFIndSize tyCtor (dataGerm ℓ tyCtor (▹⁇ ℓ) d) (dataGermIsCode ℓ tyCtor d) tt) O1 O1





codeSize : ∀ {ℓ} → ℂ ℓ → Ord
descSize : ∀  {ℓ sig} →  {cI cB : ℂ ℓ} → ℂDesc cI cB sig → Ord
elSize : ∀ {{æ : Æ}} {ℓ} (c : ℂ ℓ) → El c → Ord
-- ▹elSize : ∀ {ℓ} (c : ℂ ℓ) → ▹El c → Ord
⁇Size : ∀ {{ _ : Æ}} {ℓ} → ⁇Ty ℓ → Ord
CμSize : ∀ {{_ : Æ}} {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : DCtors tyCtor cI) {i} → ℂμ tyCtor D i → Ord
CElSize : ∀ {{ _ : Æ }} {ℓ sig} {cI cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI cB sig) (E : DCtors tyCtor cI) {i b} → ℂDescEl D (ℂμ tyCtor E) i b → Ord
-- germFArgSize : ∀ {ℓ} (tyCtor : CName) → (D : GermDesc) → (DataGermIsCode ℓ D)
--   → (cs : FContainer (interpGerm D) (W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ)) (⁇Ty ℓ) tt)
--   → □ _ (λ _ → Ord) (tt , cs)
--   → Ord

-- Marks each Unk thing as having size 1, so we'll have to always handle them with normal recursion
-- germArgSize : ∀ {ℓ} (tyCtor : CName) →  W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ) tt → Ord
germDescSize : ∀ {{_ : Æ}} {ℓ} {B} →  (D : GermCtor B)
  → (DataGermIsCode ℓ D)
  → B
  → Ord


DLim : ∀ (tyCtor : CName) → ((d : DName tyCtor) → Ord) → Ord
DLim tyCtor f with numCtors tyCtor
... | ℕ.zero = OZ
... | ℕ.suc n = OLim ⦃ æ = Approx ⦄ (CFin n) (λ x → f (fromCFin x))

DLim-cocone : ∀ (tyCtor : CName) → (f : ( DName tyCtor) → Ord) → (d : DName tyCtor) → f d ≤o DLim tyCtor f
DLim-cocone tyCtor f d with numCtors tyCtor
DLim-cocone tyCtor f () | ℕ.zero
... | ℕ.suc n  = ≤o-cocone ⦃ æ = Approx ⦄ _ ( toCFin d) (pSubst (λ x → f d ≤o f x) (pSym (fromToCFin d)) (≤o-refl _))

extDLim : ∀ (tyCtor : CName) → (f1 f2 : (d : DName tyCtor) → Ord) → (∀ d → f1 d ≤o f2 d) → (DLim tyCtor f1) ≤o (DLim tyCtor f2)
extDLim tyCtor f1 f2 lt with numCtors tyCtor
... | ℕ.zero = ≤o-Z
... | ℕ.suc n = extLim ⦃ æ = Approx ⦄ (λ x → f1 (fromCFin x)) (λ x → f2 (fromCFin x)) (λ k → lt (fromCFin k))


germDescSize  GEnd GEndCode b = O1
germDescSize  (GArg A D) (GArgCode c isom pf) b = O↑ (omax (codeSize (c b)) (OLim (c b) (λ a → germDescSize D pf (b , Iso.inv (isom b) (exact a) ))))
germDescSize  (GArg A D) (GGuardedArgCode c x₁ x₂) b = O1
germDescSize  (GRec D) (GRecCode isom pf) b = O↑ (germDescSize D pf b)
germDescSize  (GHRec A D) (GHRecCode c isom pf) b = O↑ (OLim (c b) (λ a → omax (codeSize (c b))( germDescSize  D pf b)))
germDescSize  (GHRec A D) (GGuardedHRecCode c x₁ x₂) b = O1
germDescSize  (GUnk A D) (GUnkCode c x pf) b =  O↑ (OLim (c b) λ a → omax (codeSize (c b)) (germDescSize D pf b))
germDescSize  (GUnk A D) (GGuardedUnkCode c x pf) b = O1


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
codeSize (CΠ dom cod) = O↑ (omax (omax∞ (codeSize dom)) (OLim {{æ = Approx}} dom λ x → omax∞ (codeSize (cod x))))
codeSize (CΣ dom cod) = O↑ (omax (omax∞ (codeSize dom)) ( OLim  {{æ = Approx}} dom λ x → omax∞ (codeSize (cod x))))
codeSize  (C≡ c x y) = O↑ (omax (omax∞ (codeSize c)) (omax (elSize {{Approx}} c x) (elSize {{Approx}}  c y)) )
codeSize (Cμ tyCtor c D x) = O↑ (omax (omax∞ (codeSize c)) (omax∞ (DLim tyCtor λ d → descSize (D d))))
codeSize {ℓ = suc ℓ} (CCumul c) = O↑ (codeSize c)

descSize {cI = c} (CEnd i) = O↑ (elSize {{Approx}} c i )
descSize {cB = cB} (CArg c D cB' _) = O↑ (omax (codeSize cB') (omax (OLim {{æ = Approx}} cB λ b → omax∞ (codeSize (c b))) (descSize D)))
descSize {cI = c} (CRec j D) = O↑ (omax (descSize D) (elSize {{Approx}} c j))
descSize {cI = cI} {cB = cB} (CHRec c j D cB' _) =
  O↑ (omax (omax (codeSize cB')
     (OLim {{æ = Approx}} cB λ b → omax∞ (codeSize (c b))))
    (omax
      (OLim {{æ = Approx}} cB λ b → OLim {{æ = Approx}} (c b) λ a →  (elSize {{Approx}} cI (j b a)))
      (descSize D) ))


-- There are no codes of size zero
-- noCodeZero : ∀ {ℓ} (c : ℂ ℓ) → ¬ (codeSize c ≡p OZ)
-- noCodeZero C⁇ ()
-- noCodeZero C℧ pf = {!!}
-- noCodeZero C𝟘 pf = {!!}
-- noCodeZero C𝟙 pf = {!!}
-- noCodeZero CType pf = {!!}
-- noCodeZero (CΠ c cod) pf = {!!}
-- noCodeZero (CΣ c cod) pf = {!!}
-- noCodeZero (C≡ c x y) pf = {!!}
-- noCodeZero (Cμ tyCtor c D x) pf = {!!}

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
⁇Size {ℓ = ℓ} (⁇μ tyCtor x) = O↑ ((germIndSize tyCtor x))
⁇Size {ℓ = suc ℓ} (⁇Cumul x) = O↑ (codeSize x)
-- O1 --TODO does this cause problems?
-- CμSize (dataGermCode ℓ tyCtor) (transport⁻ (dataGermCodeEq ℓ tyCtor) x)
  -- where
  --   cx : ℂμ1 tyCtor (dataGermCode ℓ tyCtor) true
  --   cx =  transport⁻ (dataGermCodeEq ℓ tyCtor) x


elSize C⁇ x = O↑ (⁇Size x)
elSize C℧ x = O1
elSize C𝟘 x = O1
elSize C𝟙 x = O1
elSize {suc ℓ} CType x = O↑ (codeSize x)
elSize (CΠ dom cod) f = O↑ (OLim dom (λ x → elSize (cod (approx x)) (f x))) -- (OLim dom λ x → elSize (cod (approx x)) (f ?))
elSize (CΣ dom cod) (x , y) = O↑ (omax (elSize dom (exact x)) (elSize (cod (approx x)) y))
elSize (C≡ c x₁ y) (x ⊢ .x₁ ≅ .y) = O↑ (elSize {{Approx}} c x)
elSize (Cμ tyCtor cI D i) x = O↑  (CμSize D (Iso.inv CμWiso x))
elSize {ℓ = suc ℓ} (CCumul c) x = elSize c x

CμSize D (Cinit d x) = O↑ (CElSize (D d) D x)
CμSize D Cμ⁇ = O1
CμSize D Cμ℧ = O1

CElSize {cI = cI} .(CEnd j) E {i} (ElEnd j (w ⊢ _ ≅ _)) = elSize {{Approx}} cI w
CElSize {{æ}} (CArg c D _ _) E {b = b} (ElArg a x) = O↑ (omax (elSize {{æ}} (c b) (exact a)) (CElSize D E x))
CElSize (CRec j D) E (ElRec x x₁) = O↑ (omax (CμSize E x) (CElSize D E x₁))
CElSize (CHRec c j D _ _) E {b = b} (ElHRec f x) = O↑ (OLim (c b) λ a → omax (CμSize E (f a)) (CElSize D E x))

-- CElSize {cI = cI} .(CEnd j) E {i} (ElEnd j (w ⊢ _ ≅ _)) = elSize {{Approx}} cI w
-- CElSize {{æ}} (CArg c D) E (ElArg a x) = O↑ (omax (elSize {{æ}} c (exact a)) (CElSize (D (approx a)) E x))
-- CElSize (CRec j D) E (ElRec x x₁) = O↑ (omax (CμSize E x) (CElSize D E x₁))
-- CElSize (CHRec c j D) E (ElHRec f x) = O↑ (OLim c λ a → omax (CμSize E (f a)) (CElSize (D (approx a)) E (x a)))
-- We can't use guarded arguments in size calcs, that's why they're guarded
-- So we use the size at the error value
-- CElSize (CHGuard c D1 D2) E (ElHGuard x x₁) = O↑ (omax (CElSize D1 E (x (next (℧ c)))) (CElSize D2 E x₁))







-- ℧size : ∀ {{_ : Æ}} {ℓ} (c : ℂ ℓ) → elSize c (℧ c) ≤o O1
-- ℧size C⁇ = {!!}
-- ℧size C℧ = {!!}
-- ℧size C𝟘 = {!!}
-- ℧size C𝟙 = {!!}
-- ℧size CType = {!!}
-- ℧size (CΠ c cod) = {!!}
-- ℧size (CΣ c cod) = {!!}
-- ℧size (C≡ c x y) = {!!}
-- ℧size (Cμ tyCtor c D x) = {!!}
-- ℧size C⁇ = ≤o-sucMono (≤o-Z)
-- ℧size C℧ = ≤o-sucMono (≤o-Z)
-- ℧size C𝟘 = ≤o-sucMono (≤o-Z)
-- ℧size C𝟙 = ≤o-sucMono (≤o-Z)
-- ℧size {suc ℓ} CType = ≤o-sucMono (≤o-Z)
-- ℧size (CΠ c cod) = ≤o-sucMono (≤o-Z)
-- ℧size ⦃ Approx ⦄ (CΣ c cod) = ≤o-sucMono (≤o-Z)
-- ℧size ⦃ Exact ⦄ (CΣ c cod) =  ≤o-limiting (λ x → elSize (cod (approx x)) (℧ (CΠ c cod) x)) λ k → ℧size (cod (approx k))
-- ℧size (C≡ c x y) = ℧size {{Approx}} c
-- ℧size (Cμ tyCtor c D x) = ≤o-refl _

codeSuc : ∀ {ℓ} (c : ℂ ℓ) → OZ <o codeSize c
codeSuc C⁇ = ≤o-refl _
codeSuc C℧ = ≤o-refl _
codeSuc C𝟘 = ≤o-refl _
codeSuc C𝟙 = ≤o-refl _
codeSuc CType = ≤o-refl _
codeSuc (CΠ c cod) = ≤o-sucMono ≤o-Z
codeSuc (CΣ c cod) = ≤o-sucMono ≤o-Z
codeSuc (C≡ c x y) = ≤o-sucMono ≤o-Z
codeSuc (Cμ tyCtor c D x) = ≤o-sucMono ≤o-Z
codeSuc {ℓ = suc ℓ} (CCumul c) = ≤o-trans (codeSuc c) (≤↑ (codeSize c))

codeMaxL : ∀ {ℓ} (c : ℂ ℓ) → omax O1 (codeSize c) ≤o codeSize c
codeMaxL CodeModule.C⁇ = omax-oneL
codeMaxL CodeModule.C℧ = omax-oneL
codeMaxL CodeModule.C𝟘 = omax-oneL
codeMaxL CodeModule.C𝟙 = omax-oneL
codeMaxL CodeModule.CType = omax-oneL
codeMaxL (CodeModule.CΠ c cod) = omax-oneL
codeMaxL (CodeModule.CΣ c cod) = omax-oneL
codeMaxL (CodeModule.C≡ c x y) = omax-oneL
codeMaxL (CodeModule.Cμ tyCtor c D x) = omax-oneL
codeMaxL {ℓ = suc ℓ} (CCumul c) = omax-oneL


codeMaxR : ∀ {ℓ} (c : ℂ ℓ) → omax (codeSize c) O1 ≤o codeSize c
codeMaxR CodeModule.C⁇ = omax-oneR
codeMaxR CodeModule.C℧ = omax-oneR
codeMaxR CodeModule.C𝟘 = omax-oneR
codeMaxR CodeModule.C𝟙 = omax-oneR
codeMaxR CodeModule.CType = omax-oneR
codeMaxR (CodeModule.CΠ c cod) = omax-oneR
codeMaxR (CodeModule.CΣ c cod) = omax-oneR
codeMaxR (CodeModule.C≡ c x y) = omax-oneR
codeMaxR (CodeModule.Cμ tyCtor c D x) = omax-oneR
codeMaxR {ℓ = suc ℓ} (CCumul c) = omax-oneR


⁇suc : ∀ {{_ : Æ}} {ℓ} (x : ⁇Ty ℓ) → O1 ≤o ⁇Size x
⁇suc ⁇⁇ = ≤o-sucMono ≤o-Z
⁇suc ⁇℧ = ≤o-sucMono ≤o-Z
⁇suc ⁇𝟙 = ≤o-sucMono ≤o-Z
⁇suc {suc ℓ} (⁇Type x) = ≤o-sucMono ≤o-Z
⁇suc (⁇Π x) = ≤o-sucMono ≤o-Z
⁇suc (⁇Σ x) = ≤o-sucMono ≤o-Z
⁇suc (⁇≡ (x ⊢ .⁇⁇ ≅ .⁇⁇)) = ≤o-sucMono ≤o-Z
⁇suc (⁇μ tyCtor x) = ≤o-sucMono ≤o-Z
⁇suc {ℓ = suc ℓ} (⁇Cumul c) = ≤o-sucMono ≤o-Z

open import Cubical.Data.Maybe


dataGermDescSize : {{_ : Æ}} → ℕ → CName → Ord
dataGermDescSize ℓ tyCtor with numCtors tyCtor in deq
... | ℕ.zero = O1
... | ℕ.suc n = OLim {{æ = Approx}} (CFin n) λ x →
  let
    d : DName tyCtor
    d = pSubst Fin (pSym deq) (fromCFin x)
  in germDescSize (dataGerm ℓ tyCtor (▹⁇ ℓ) d) (dataGermIsCode ℓ tyCtor d) tt


record DataGermsSmaller : Set2 where
  field
    dataGermSmaller : ∀ {{_ : Æ}} (ℓ) tyCtor {pars : ApproxEl (Params ℓ tyCtor)} {indices} → dataGermDescSize ℓ tyCtor ≤o descSize (descFor ℓ tyCtor pars indices)

open DataGermsSmaller {{...}} public


-- Used for well-founded 2-argument induction
-- descPairSize : ∀ {{_ : Æ}} {ℓ sig} →  {cI cB cI' cB' : ℂ ℓ} → (D1 : ℂDesc cI cB sig) (D2 : ℂDesc cI' cB' sig) → Ord

-- codePairSize c1 c2 with codeHead c1 in eq1 | codeHead c2 in eq2 | headMatchView (codeHead c1) (codeHead c2)
-- ... | h1 |  h2 |  H℧L x = codeSize c2
-- ... | h1 |  h2 |  H℧R x = codeSize c1
-- ... | h1 |  h2 |  H⁇L x x₁ = codeSize c2
-- ... | .(HStatic _) |  h2 |  H⁇R x = codeSize c1
-- ... | .(HStatic _) |  .(HStatic _) |  HNeq x = omax (codeSize c1) (codeSize c2)
-- codePairSize (CΠ dom1 cod1) (CΠ dom2 cod2) | HStatic HΠ |  HStatic _ |  HEq reflp
--   = O↑ (omax (codePairSize dom1 dom2) (OLim dom1 λ x1 → OLim dom2 λ x2 → codePairSize (cod1 (approx x1)) (cod2 (approx x2))))
-- codePairSize (CΣ dom1 cod1) (CΣ dom2 cod2) | HStatic HΣ |  HStatic _ |  HEq reflp
--    = O↑ (omax (codePairSize dom1 dom2) (OLim dom1 λ x1 → OLim dom2 λ x2 → codePairSize (cod1 (approx x1)) (cod2 (approx x2))))
-- codePairSize (C≡ c1 x y) (C≡ c2 x₁ y₁) | HStatic H≅ |  HStatic _ |  HEq reflp
--   = O↑ (codePairSize c1 c2)
-- codePairSize C𝟙 C𝟙 | HStatic H𝟙 |  HStatic _ |  HEq reflp = O1
-- codePairSize C𝟘 C𝟘 | HStatic H𝟘 |  HStatic _ |  HEq reflp = O1
-- codePairSize CType CType | HStatic HType |  HStatic _ |  HEq reflp = O1
-- codePairSize (Cμ tyCtor c1 D x) (Cμ tyCtor₁ c2 D₁ x₁) | HStatic (HCtor x₂) |  HStatic _ |  HEq reflp with reflp ← eq1 with reflp ← eq2
--   = O↑ (DLim tyCtor λ d → descPairSize (D d) (D₁ d))


-- descPairSize (CEnd i) (CEnd i₁) = O1
-- descPairSize {cB = cB} {cB' = cB'} (CArg c D1) (CArg c' D2)
--   = O↑ (omax (OLim cB λ x1 → OLim cB' λ x2 → codePairSize (c (approx x1)) (c' (approx x2)) ) (descPairSize D1 D2))
-- descPairSize (CRec j D1) (CRec j' D2)
--   = O↑ (descPairSize  D1 D2)
-- descPairSize {cB = cB} {cB' = cB'} (CHRec c j D1) (CHRec c' j' D2)
--   = O↑ (omax (OLim cB λ x1 → OLim cB' λ x2 → codePairSize (c (approx x1)) (c' (approx x2)) ) (descPairSize D1 D2))


-- Sizes for well-formed codes
-- wfSize : ∀ {ℓ} → ℂwf ℓ → Ord
-- wfSize c = codeSize (code c)

-- wfElSize : ∀ {{_ : Æ}} {ℓ} → (c : ℂwf ℓ) → wfEl c → Ord
-- wfElSize c x = elSize (code c) x




-- wfPairSize : ∀ {ℓ} (c1 c2 : ℂwf ℓ) → Ord
-- wfPairSize c1 c2 = csize (codePairSize (code c1) (code c2))



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
-- -- elSizeLowerBound (Cμ tyCtor c D x₁) W⁇ = ≤o-sucMono ≤o-Z

-- -- ⁇SizeLowerBound ⁇⁇ = ≤o-refl _
-- -- ⁇SizeLowerBound ⁇℧ = ≤o-refl _
-- -- ⁇SizeLowerBound ⁇𝟙 = ≤o-refl _
-- -- ⁇SizeLowerBound {suc ℓ} (⁇Type x) = codeSizeLowerBound x
-- -- ⁇SizeLowerBound (⁇Π x) = ≤o-sucMono ≤o-Z
-- -- ⁇SizeLowerBound (⁇Σ x) = ≤o-sucMono ≤o-Z
-- -- ⁇SizeLowerBound (⁇≡ (x ⊢ _ ≅ _)) = ≤o-sucMono ≤o-Z
-- -- ⁇SizeLowerBound (⁇μ tyCtor x) = ≤o-sucMono ≤o-Z

-- -- onePlusCode-L : ∀ {ℓ} {c1 c2 : ℂ ℓ} → codeSize c1 <o ((codeSize c1) +o (codeSize c2))
-- -- onePlusCode-L {c1 = c1} {c2} with (o1 , pf1) ← codeSuc c1 | (o2 , pf2) ← codeSuc c2 rewrite pf1 rewrite pf2 = ≤o-sucMono (≤o-trans (≤o-sucMono (+o-≤-L o1 o2)) (oplus-suc-swap o1 o2))

-- -- onePlusCode-R : ∀ {ℓ} {c1 c2 : ℂ ℓ} → codeSize c2 <o ((codeSize c1) +o (codeSize c2))
-- -- onePlusCode-R {c1 = c1} {c2} with (o1 , pf1) ← codeSuc c1 | (o2 , pf2) ← codeSuc c2 rewrite pf1 rewrite pf2 = ≤o-sucMono (≤o-trans (≤o-sucMono (+o-≤-R o1 o2)) (oplus-suc-swap o1 o2))
