

{-# OPTIONS --cubical --guarded #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Vec
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


open import SizeOrdMultiMax public





open import Code
open import WMuEq
open import Head
open import Util

open import SizeOrd -- ℂ El ℧ C𝟙 refl



-- germSize {ℓ} tyCtor = wInd (λ _ → LargeSize) (germDescFSize tyCtor (GArg (DName tyCtor) (dataGerm ℓ tyCtor (▹⁇ ℓ)))) LO1 LO1

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
  → □ _ (λ _ → Size) (tt , cs)
  → Size
germIndSize : ∀ {{ _ : Æ }} {ℓ} (tyCtor : CName) →  W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ) tt → Size


germFIndSize tyCtor GEnd GEndCode b (FC com k unk) φ = S1
germFIndSize tyCtor (GRec D) (GRecCode c pf) b (FC com k unk) φ =
  S↑ (smax (φ (Rec tt)) (germFIndSize tyCtor D pf b (FC com (λ r → k (Rest r)) unk) (λ r → φ (Rest r))))
germFIndSize tyCtor (GArg A D) (GArgCode c isom pf) b (FC (a , com) k unk) φ = S↑ (germFIndSize tyCtor D pf (b , a) (FC com k unk) φ)
germFIndSize tyCtor (GArg A D) (GGuardedArgCode c x pf) b (FC com k unk) φ = S1
germFIndSize {{æ}} tyCtor (GHRec A D) (GHRecCode c isom pf) b (FC com k unk) φ = S↑ (SLim (c b) helper)
  where
    helper : Approxed (λ {{æ}} → El {{æ = æ}} (c b))  → Size
    helper a = smax (φ (Rec ac)) (germFIndSize tyCtor D pf b (FC com (λ r → k (Rest (ac , r))) unk) λ r → φ (Rest (ac , r)))
      where
        ac : A b
        ac = Iso.inv (isom b) (exact a)
germFIndSize tyCtor (GHRec A D) (GGuardedHRecCode c x pf) b (FC com k unk) φ = S1
germFIndSize tyCtor (GUnk A D) (GUnkCode c isom pf) b (FC com k unk) φ = S↑ (SLim (c b) helper)
  where
    helper : Approxed (λ {{æ}} → El {{æ = æ}} (c b))  → Size
    helper a =  germFIndSize tyCtor D pf b (FC com k λ r → unk (Rest ((ac , r)))) φ
      where
        ac : A b
        ac = Iso.inv (isom b) (exact a)
germFIndSize tyCtor (GUnk A D) (GGuardedUnkCode c x pf) b (FC com k unk) φ = S1


germIndSize {ℓ} tyCtor = wRecArg tyCtor Size (λ d → germFIndSize tyCtor (dataGerm ℓ tyCtor (▹⁇ ℓ) d) (dataGermIsCode ℓ tyCtor d) tt) S1 S1



DLim : ∀ (tyCtor : CName) → ((d : DName tyCtor) → Size) → Size
DLim tyCtor f with numCtors tyCtor
... | ℕ.zero = SZ
... | ℕ.suc n = SLim ⦃ æ = Approx ⦄ (CFin n) (λ x → f (fromCFin x))

DLim-cocone : ∀ (tyCtor : CName) → (f : ( DName tyCtor) → Size) → (d : DName tyCtor) → f d ≤ₛ DLim tyCtor f
DLim-cocone tyCtor f d with numCtors tyCtor
DLim-cocone tyCtor f () | ℕ.zero
... | ℕ.suc n  = pSubst (λ x → f d ≤ₛ f x) (pSym (fromToCFin d)) ≤ₛ-refl ≤⨟ ≤ₛ-cocone ⦃ æ = Approx ⦄ (toCFin d)

extDLim : ∀ (tyCtor : CName) → (f1 f2 : (d : DName tyCtor) → Size) → (∀ d → f1 d ≤ₛ f2 d) → (DLim tyCtor f1) ≤ₛ (DLim tyCtor f2)
extDLim tyCtor f1 f2 lt with numCtors tyCtor
... | ℕ.zero = ≤ₛ-Z
... | ℕ.suc n = ≤ₛ-extLim ⦃ æ = Approx ⦄ (λ k → lt (fromCFin k))

smax-DLim2 : ∀ (tyCtor : CName) → (f1 f2 : (d : DName tyCtor) → Size) →  DLim tyCtor (λ d1 → DLim tyCtor (λ d2 → smax (f1 d1) (f2 d2))) ≤ₛ smax (DLim tyCtor f1) (DLim tyCtor f2)
smax-DLim2 tyCtor f1 f2 with numCtors tyCtor
... | ℕ.zero = ≤ₛ-Z
... | ℕ.suc n = smax-lim2L (λ z → f1 (fromCFin z)) (λ z → f2 (fromCFin z))

-- Marks each Unk thing as having size 1, so we'll have to always handle them with normal recursion
-- germArgSize : ∀ {ℓ} (tyCtor : CName) →  W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ) tt → Size
germDescSize : ∀ {{_ : Æ}} {ℓ} {B} →  (D : GermCtor B)
  → (DataGermIsCode ℓ D)
  → B
  → Size
codeSize : ∀ {ℓ} → ℂ ℓ → Size
descSize : ∀  {ℓ sig} →  {cI cB : ℂ ℓ} → ℂDesc cI cB sig → Size


codeSize C⁇ = S1
codeSize C℧ = S1
codeSize C𝟘 = S1
codeSize C𝟙 = S1
codeSize CType = S1
codeSize (CΠ dom cod) =
  S↑ (smax
    ( (codeSize dom))
    ( (SLim {{æ = Approx}} dom λ x →  (codeSize (cod x)))))
codeSize (CΣ dom cod) =
  S↑ (smax
    ( (codeSize dom))
    (  (SLim  {{æ = Approx}} dom λ x →  (codeSize (cod x)))))
codeSize  (C≡ c x y) = S↑ ( (codeSize c))
codeSize (Cμ tyCtor c D x) =
  S↑ (smax
    ( (codeSize c))
    ( (DLim tyCtor λ d → descSize (D d))))
codeSize {ℓ = suc ℓ} (CCumul c) = S↑ (codeSize c)

--TODO: need ElSizes here?
descSize {cI = c} (CEnd i) = S1 -- S↑ (elSize {{Approx}} c i )
descSize {cB = cB} (CArg c D cB' _) = S↑
  (smax* (
    (codeSize cB')
    ∷ (SLim {{æ = Approx}} cB λ b →  (codeSize (c b)))
    ∷ (descSize D) ∷ [])
    )
descSize {cI = c} (CRec j D) = S↑  (descSize D)
descSize {cI = cI} {cB = cB} (CHRec c j D cB' _) =
  S↑ (smax* (
    (codeSize cB')
    ∷ (SLim {{æ = Approx}} cB λ b →  (codeSize (c b)))
    ∷  (descSize D) ∷ [] ))


germDescSize  GEnd GEndCode b = S1
germDescSize  (GArg A D) (GArgCode c isom pf) b = S↑ (smax (codeSize (c b)) (SLim (c b) (λ a → germDescSize D pf (b , Iso.inv (isom b) (exact a) ))))
germDescSize  (GArg A D) (GGuardedArgCode c x₁ x₂) b = S1
germDescSize  (GRec D) (GRecCode isom pf) b = S↑ (germDescSize D pf b)
germDescSize  (GHRec A D) (GHRecCode c isom pf) b = S↑ (SLim (c b) (λ a → smax (codeSize (c b))( germDescSize  D pf b)))
germDescSize  (GHRec A D) (GGuardedHRecCode c x₁ x₂) b = S1
germDescSize  (GUnk A D) (GUnkCode c x pf) b =  S↑ (SLim (c b) λ a → smax (codeSize (c b)) (germDescSize D pf b))
germDescSize  (GUnk A D) (GGuardedUnkCode c x pf) b = S1




elSize : ∀ {{æ : Æ}} {ℓ} (c : ℂ ℓ) → El c → Size
-- ▹elSize : ∀ {ℓ} (c : ℂ ℓ) → ▹El c → Size
⁇Size : ∀ {{ _ : Æ}} {ℓ} → ⁇Ty ℓ → Size
CμSize : ∀ {{_ : Æ}} {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : DCtors tyCtor cI) {i} → ℂμ tyCtor D i → Size
CElSize : ∀ {{ _ : Æ }} {ℓ sig} {cI cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI cB sig) (E : DCtors tyCtor cI) {i b} → ℂDescEl D (ℂμ tyCtor E) i b → Size
-- germFArgSize : ∀ {ℓ} (tyCtor : CName) → (D : GermDesc) → (DataGermIsCode ℓ D)
--   → (cs : FContainer (interpGerm D) (W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ)) (⁇Ty ℓ) tt)
--   → □ _ (λ _ → Size) (tt , cs)
--   → Size





-- germFArgSize tyCtor GEnd GEndCode (FC com k unk) φ = S1
-- germFArgSize tyCtor (GArg A D) (GArgCode c x₁ x₂) (FC (a , com) k unk) φ = (codeSize c)
-- germFArgSize tyCtor (GArg A D) (GGuardedArgCode c x₂ x₃) x φ = S1
-- germFArgSize tyCtor (GHRec A D) (GHRecCode c x₂ x₃) x φ = S1 -- SLim c (λ a → germFArgSize tyCtor {!!} {!!} {!!} {!!})
-- germFArgSize tyCtor (GHRec A D) (GGuardedHRecCode c x₂ x₃) x φ = S1
-- germFArgSize tyCtor (GUnk A D) (GUnkCode c x₁ pf) x φ = {!!}
-- germFArgSize tyCtor (GUnk A D) (GGuardedUnkCode c x₁ pf) x φ = S1

-- germArgSize {ℓ} tyCtor = wRecArg tyCtor Size (λ d → germFArgSize tyCtor (dataGerm ℓ tyCtor (▹⁇ ℓ) d) (dataGermIsCode ℓ tyCtor d)) S1 S1



-- There are no codes of size zero
-- noCodeZero : ∀ {ℓ} (c : ℂ ℓ) → ¬ (codeSize c ≡p SZ)
-- noCodeZero C⁇ ()
-- noCodeZero C℧ pf = {!!}
-- noCodeZero C𝟘 pf = {!!}
-- noCodeZero C𝟙 pf = {!!}
-- noCodeZero CType pf = {!!}
-- noCodeZero (CΠ c cod) pf = {!!}
-- noCodeZero (CΣ c cod) pf = {!!}
-- noCodeZero (C≡ c x y) pf = {!!}
-- noCodeZero (Cμ tyCtor c D x) pf = {!!}

-- argLessLeft : ∀ o1 o2 → o1 <o S↑ (smax o1 o2)
-- argLessLeft o1 o2 = ≤ₛ-sucMono smax-≤L

-- argLessRight : ∀ o1 o2 → o2 <o S↑ (smax o1 o2)
-- argLessRight o1 o2 = ≤ₛ-sucMono smax-≤R







⁇Size ⁇⁇ = S1
⁇Size ⁇℧ = S1
⁇Size ⁇𝟙 = S1
⁇Size {ℓ = ℕ.suc ℓ} (⁇Type x) = S↑  (codeSize x)
⁇Size (⁇Π f) = S↑ (SLim C⁇ (λ x → ⁇Size (f (transport (sym hollowEq) (next (exact x)))))) -- S↑ (SLim C⁇ (λ x → LUnk æ ))
⁇Size (⁇Σ (x , y)) = S↑ (smax (⁇Size x) (⁇Size y))
⁇Size (⁇≡ (x ⊢ .⁇⁇ ≅ .⁇⁇)) = S↑ (⁇Size x)
⁇Size {ℓ = ℓ} (⁇μ tyCtor x) = S↑ ((germIndSize tyCtor x))
⁇Size {ℓ = suc ℓ} (⁇Cumul c x) = S↑ (codeSize c) --TODO: is this okay? Should be, since going one universe lower
-- S1 --TODO does this cause problems?
-- CμSize (dataGermCode ℓ tyCtor) (transport⁻ (dataGermCodeEq ℓ tyCtor) x)
  -- where
  --   cx : ℂμ1 tyCtor (dataGermCode ℓ tyCtor) true
  --   cx =  transport⁻ (dataGermCodeEq ℓ tyCtor) x


elSize C⁇ x = S↑ (⁇Size x)
elSize C℧ x = S1
elSize C𝟘 x = S1
elSize C𝟙 x = S1
elSize {suc ℓ} CType x = S↑ (codeSize x)
elSize (CΠ dom cod) f = S↑ (SLim dom (λ x → elSize (cod (approx x)) (f x))) -- (SLim dom λ x → elSize (cod (approx x)) (f ?))
elSize (CΣ dom cod) (x , y) = S↑ (smax (elSize dom (exact x)) (elSize (cod (approx x)) y))
elSize (C≡ c x₁ y) (x ⊢ .x₁ ≅ .y) = S↑ (elSize {{Approx}} c x)
elSize (Cμ tyCtor cI D i) x = S↑  (CμSize D (Iso.inv CμWiso x))
elSize {ℓ = suc ℓ} (CCumul c) x = elSize c x

CμSize D (Cinit d x) = S↑ (CElSize (D d) D x)
CμSize D Cμ⁇ = S1
CμSize D Cμ℧ = S1

CElSize {cI = cI} .(CEnd j) E {i} (ElEnd j (w ⊢ _ ≅ _)) = elSize {{Approx}} cI w
CElSize {{æ}} (CArg c D _ _) E {b = b} (ElArg a x) = S↑ (smax (elSize {{æ}} (c b) (exact a)) (CElSize D E x))
CElSize (CRec j D) E (ElRec x x₁) = S↑ (smax (CμSize E x) (CElSize D E x₁))
CElSize (CHRec c j D _ _) E {b = b} (ElHRec f x) = S↑ (SLim (c b) λ a → smax (CμSize E (f a)) (CElSize D E x))

-- CElSize {cI = cI} .(CEnd j) E {i} (ElEnd j (w ⊢ _ ≅ _)) = elSize {{Approx}} cI w
-- CElSize {{æ}} (CArg c D) E (ElArg a x) = S↑ (smax (elSize {{æ}} c (exact a)) (CElSize (D (approx a)) E x))
-- CElSize (CRec j D) E (ElRec x x₁) = S↑ (smax (CμSize E x) (CElSize D E x₁))
-- CElSize (CHRec c j D) E (ElHRec f x) = S↑ (SLim c λ a → smax (CμSize E (f a)) (CElSize (D (approx a)) E (x a)))
-- We can't use guarded arguments in size calcs, that's why they're guarded
-- So we use the size at the error value
-- CElSize (CHGuard c D1 D2) E (ElHGuard x x₁) = S↑ (smax (CElSize D1 E (x (next (℧ c)))) (CElSize D2 E x₁))







-- ℧size : ∀ {{_ : Æ}} {ℓ} (c : ℂ ℓ) → elSize c (℧ c) ≤ₛ S1
-- ℧size C⁇ = {!!}
-- ℧size C℧ = {!!}
-- ℧size C𝟘 = {!!}
-- ℧size C𝟙 = {!!}
-- ℧size CType = {!!}
-- ℧size (CΠ c cod) = {!!}
-- ℧size (CΣ c cod) = {!!}
-- ℧size (C≡ c x y) = {!!}
-- ℧size (Cμ tyCtor c D x) = {!!}
-- ℧size C⁇ = ≤ₛ-sucMono (≤ₛ-Z)
-- ℧size C℧ = ≤ₛ-sucMono (≤ₛ-Z)
-- ℧size C𝟘 = ≤ₛ-sucMono (≤ₛ-Z)
-- ℧size C𝟙 = ≤ₛ-sucMono (≤ₛ-Z)
-- ℧size {suc ℓ} CType = ≤ₛ-sucMono (≤ₛ-Z)
-- ℧size (CΠ c cod) = ≤ₛ-sucMono (≤ₛ-Z)
-- ℧size ⦃ Approx ⦄ (CΣ c cod) = ≤ₛ-sucMono (≤ₛ-Z)
-- ℧size ⦃ Exact ⦄ (CΣ c cod) =  ≤ₛ-limiting (λ x → elSize (cod (approx x)) (℧ (CΠ c cod) x)) λ k → ℧size (cod (approx k))
-- ℧size (C≡ c x y) = ℧size {{Approx}} c
-- ℧size (Cμ tyCtor c D x) = ≤ₛ-refl _

codeSuc : ∀ {ℓ} (c : ℂ ℓ) → SZ <ₛ codeSize c
codeSuc C⁇ = ≤ₛ-refl
codeSuc C℧ = ≤ₛ-refl
codeSuc C𝟘 = ≤ₛ-refl
codeSuc C𝟙 = ≤ₛ-refl
codeSuc CType = ≤ₛ-refl
codeSuc (CΠ c cod) = ≤ₛ-sucMono ≤ₛ-Z
codeSuc (CΣ c cod) = ≤ₛ-sucMono ≤ₛ-Z
codeSuc (C≡ c x y) = ≤ₛ-sucMono ≤ₛ-Z
codeSuc (Cμ tyCtor c D x) = ≤ₛ-sucMono ≤ₛ-Z
codeSuc {ℓ = suc ℓ} (CCumul c) = (codeSuc c) ≤⨟ (≤↑ (codeSize c))

codeMaxL : ∀ {ℓ} (c : ℂ ℓ) → smax S1 (codeSize c) ≤ₛ codeSize c
codeMaxL CodeModule.C⁇ = smax-oneL
codeMaxL CodeModule.C℧ = smax-oneL
codeMaxL CodeModule.C𝟘 = smax-oneL
codeMaxL CodeModule.C𝟙 = smax-oneL
codeMaxL CodeModule.CType = smax-oneL
codeMaxL (CodeModule.CΠ c cod) = smax-oneL
codeMaxL (CodeModule.CΣ c cod) = smax-oneL
codeMaxL (CodeModule.C≡ c x y) = smax-oneL
codeMaxL (CodeModule.Cμ tyCtor c D x) = smax-oneL
codeMaxL {ℓ = suc ℓ} (CCumul c) = smax-oneL


codeMaxR : ∀ {ℓ} (c : ℂ ℓ) → smax (codeSize c) S1 ≤ₛ codeSize c
codeMaxR CodeModule.C⁇ = smax-oneR
codeMaxR CodeModule.C℧ = smax-oneR
codeMaxR CodeModule.C𝟘 = smax-oneR
codeMaxR CodeModule.C𝟙 = smax-oneR
codeMaxR CodeModule.CType = smax-oneR
codeMaxR (CodeModule.CΠ c cod) = smax-oneR
codeMaxR (CodeModule.CΣ c cod) = smax-oneR
codeMaxR (CodeModule.C≡ c x y) = smax-oneR
codeMaxR (CodeModule.Cμ tyCtor c D x) = smax-oneR
codeMaxR {ℓ = suc ℓ} (CCumul c) = smax-oneR

codeMaxSuc : ∀ {ℓ1 ℓ2} {c1 : ℂ ℓ1 } {c2 : ℂ ℓ2} → S1 ≤ₛ smax (codeSize c1) (codeSize c2)
codeMaxSuc {c1 = c1} {c2 = c2} = ≤ₛ-sucMono ≤ₛ-Z ≤⨟ smax-strictMono (codeSuc c1) (codeSuc c2)


⁇suc : ∀ {{_ : Æ}} {ℓ} (x : ⁇Ty ℓ) → S1 ≤ₛ ⁇Size x
⁇suc ⁇⁇ = ≤ₛ-sucMono ≤ₛ-Z
⁇suc ⁇℧ = ≤ₛ-sucMono ≤ₛ-Z
⁇suc ⁇𝟙 = ≤ₛ-sucMono ≤ₛ-Z
⁇suc {suc ℓ} (⁇Type x) = ≤ₛ-sucMono ≤ₛ-Z
⁇suc (⁇Π x) = ≤ₛ-sucMono ≤ₛ-Z
⁇suc (⁇Σ x) = ≤ₛ-sucMono ≤ₛ-Z
⁇suc (⁇≡ (x ⊢ .⁇⁇ ≅ .⁇⁇)) = ≤ₛ-sucMono ≤ₛ-Z
⁇suc (⁇μ tyCtor x) = ≤ₛ-sucMono ≤ₛ-Z
⁇suc {ℓ = suc ℓ} (⁇Cumul c x) = ≤ₛ-sucMono ≤ₛ-Z

open import Cubical.Data.Maybe


dataGermDescSize : {{_ : Æ}} → ℕ → CName → Size
dataGermDescSize ℓ tyCtor with numCtors tyCtor in deq
... | ℕ.zero = S1
... | ℕ.suc n = SLim {{æ = Approx}} (CFin n) λ x →
  let
    d : DName tyCtor
    d = pSubst Fin (pSym deq) (fromCFin x)
  in germDescSize (dataGerm ℓ tyCtor (▹⁇ ℓ) d) (dataGermIsCode ℓ tyCtor d) tt




-- Used for well-founded 2-argument induction
-- descPairSize : ∀ {{_ : Æ}} {ℓ sig} →  {cI cB cI' cB' : ℂ ℓ} → (D1 : ℂDesc cI cB sig) (D2 : ℂDesc cI' cB' sig) → Size

-- codePairSize c1 c2 with codeHead c1 in eq1 | codeHead c2 in eq2 | headMatchView (codeHead c1) (codeHead c2)
-- ... | h1 |  h2 |  H℧L x = codeSize c2
-- ... | h1 |  h2 |  H℧R x = codeSize c1
-- ... | h1 |  h2 |  H⁇L x x₁ = codeSize c2
-- ... | .(HStatic _) |  h2 |  H⁇R x = codeSize c1
-- ... | .(HStatic _) |  .(HStatic _) |  HNeq x = smax (codeSize c1) (codeSize c2)
-- codePairSize (CΠ dom1 cod1) (CΠ dom2 cod2) | HStatic HΠ |  HStatic _ |  HEq reflp
--   = S↑ (smax (codePairSize dom1 dom2) (SLim dom1 λ x1 → SLim dom2 λ x2 → codePairSize (cod1 (approx x1)) (cod2 (approx x2))))
-- codePairSize (CΣ dom1 cod1) (CΣ dom2 cod2) | HStatic HΣ |  HStatic _ |  HEq reflp
--    = S↑ (smax (codePairSize dom1 dom2) (SLim dom1 λ x1 → SLim dom2 λ x2 → codePairSize (cod1 (approx x1)) (cod2 (approx x2))))
-- codePairSize (C≡ c1 x y) (C≡ c2 x₁ y₁) | HStatic H≅ |  HStatic _ |  HEq reflp
--   = S↑ (codePairSize c1 c2)
-- codePairSize C𝟙 C𝟙 | HStatic H𝟙 |  HStatic _ |  HEq reflp = S1
-- codePairSize C𝟘 C𝟘 | HStatic H𝟘 |  HStatic _ |  HEq reflp = S1
-- codePairSize CType CType | HStatic HType |  HStatic _ |  HEq reflp = S1
-- codePairSize (Cμ tyCtor c1 D x) (Cμ tyCtor₁ c2 D₁ x₁) | HStatic (HCtor x₂) |  HStatic _ |  HEq reflp with reflp ← eq1 with reflp ← eq2
--   = S↑ (DLim tyCtor λ d → descPairSize (D d) (D₁ d))


-- descPairSize (CEnd i) (CEnd i₁) = S1
-- descPairSize {cB = cB} {cB' = cB'} (CArg c D1) (CArg c' D2)
--   = S↑ (smax (SLim cB λ x1 → SLim cB' λ x2 → codePairSize (c (approx x1)) (c' (approx x2)) ) (descPairSize D1 D2))
-- descPairSize (CRec j D1) (CRec j' D2)
--   = S↑ (descPairSize  D1 D2)
-- descPairSize {cB = cB} {cB' = cB'} (CHRec c j D1) (CHRec c' j' D2)
--   = S↑ (smax (SLim cB λ x1 → SLim cB' λ x2 → codePairSize (c (approx x1)) (c' (approx x2)) ) (descPairSize D1 D2))


-- Sizes for well-formed codes
-- wfSize : ∀ {ℓ} → ℂwf ℓ → Size
-- wfSize c = codeSize (code c)

-- wfElSize : ∀ {{_ : Æ}} {ℓ} → (c : ℂwf ℓ) → wfEl c → Size
-- wfElSize c x = elSize (code c) x




-- wfPairSize : ∀ {ℓ} (c1 c2 : ℂwf ℓ) → Size
-- wfPairSize c1 c2 = csize (codePairSize (code c1) (code c2))



-- -- elSizeLowerBound : ∀ {ℓ} (c : ℂ ℓ) → (x : El c) → S1 ≤ₛ elSize c x
-- -- ⁇SizeLowerBound : ∀ {ℓ} (x : ⁇Ty ℓ) → S1 ≤ₛ ⁇Size x
-- -- codeSizeLowerBound : ∀ {ℓ} (c : ℂ ℓ) → S1 ≤ₛ codeSize c

-- -- codeSizeLowerBound C⁇ = ≤ₛ-refl
-- -- codeSizeLowerBound C℧ = ≤ₛ-refl
-- -- codeSizeLowerBound C𝟘 = ≤ₛ-refl
-- -- codeSizeLowerBound C𝟙 = ≤ₛ-refl
-- -- codeSizeLowerBound CType = ≤ₛ-refl
-- -- codeSizeLowerBound (CΠ c cod) = ≤ₛ-sucMono ≤ₛ-Z
-- -- codeSizeLowerBound (CΣ c cod) = ≤ₛ-sucMono ≤ₛ-Z
-- -- codeSizeLowerBound (C≡ c x y) = ≤ₛ-sucMono ≤ₛ-Z
-- -- codeSizeLowerBound (Cμ tyCtor c D x) with numCtors tyCtor
-- -- ... | ℕ.zero = ≤ₛ-refl
-- -- ... | ℕ.suc n = ≤ₛ-sucMono ≤ₛ-Z

-- -- elSizeLowerBound C⁇ x = ⁇SizeLowerBound x
-- -- elSizeLowerBound C℧ x = ≤ₛ-refl
-- -- elSizeLowerBound C𝟘 x = ≤ₛ-refl
-- -- elSizeLowerBound C𝟙 x = ≤ₛ-refl
-- -- elSizeLowerBound {suc ℓ} CType x = codeSizeLowerBound x
-- -- elSizeLowerBound (CΠ dom cod) f = underLim S1 (λ x → elSize (cod (approx x)) (f x)) (λ k → elSizeLowerBound (cod k) (f k))
-- -- elSizeLowerBound (CΣ c cod) (x , y) = ≤ₛ-trans (elSizeLowerBound c x) smax-≤L
-- -- elSizeLowerBound (C≡ c x₁ y) (x ⊢ _ ≅ _) = elSizeLowerBound c x
-- -- elSizeLowerBound (Cμ tyCtor c D x₁) (Wsup x) = ≤ₛ-sucMono ≤ₛ-Z
-- -- elSizeLowerBound (Cμ tyCtor c D x₁) W⁇ = ≤ₛ-sucMono ≤ₛ-Z

-- -- ⁇SizeLowerBound ⁇⁇ = ≤ₛ-refl
-- -- ⁇SizeLowerBound ⁇℧ = ≤ₛ-refl
-- -- ⁇SizeLowerBound ⁇𝟙 = ≤ₛ-refl
-- -- ⁇SizeLowerBound {suc ℓ} (⁇Type x) = codeSizeLowerBound x
-- -- ⁇SizeLowerBound (⁇Π x) = ≤ₛ-sucMono ≤ₛ-Z
-- -- ⁇SizeLowerBound (⁇Σ x) = ≤ₛ-sucMono ≤ₛ-Z
-- -- ⁇SizeLowerBound (⁇≡ (x ⊢ _ ≅ _)) = ≤ₛ-sucMono ≤ₛ-Z
-- -- ⁇SizeLowerBound (⁇μ tyCtor x) = ≤ₛ-sucMono ≤ₛ-Z

-- -- onePlusCode-L : ∀ {ℓ} {c1 c2 : ℂ ℓ} → codeSize c1 <o ((codeSize c1) +o (codeSize c2))
-- -- onePlusCode-L {c1 = c1} {c2} with (o1 , pf1) ← codeSuc c1 | (o2 , pf2) ← codeSuc c2 rewrite pf1 rewrite pf2 = ≤ₛ-sucMono (≤ₛ-trans (≤ₛ-sucMono (+o-≤-L o1 o2)) (oplus-suc-swap o1 o2))

-- -- onePlusCode-R : ∀ {ℓ} {c1 c2 : ℂ ℓ} → codeSize c2 <o ((codeSize c1) +o (codeSize c2))
-- -- onePlusCode-R {c1 = c1} {c2} with (o1 , pf1) ← codeSuc c1 | (o2 , pf2) ← codeSuc c2 rewrite pf1 rewrite pf2 = ≤ₛ-sucMono (≤ₛ-trans (≤ₛ-sucMono (+o-≤-R o1 o2)) (oplus-suc-swap o1 o2))
