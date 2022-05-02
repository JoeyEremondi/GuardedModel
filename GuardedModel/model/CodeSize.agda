
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

-- Brouwer Tree ordinals
-- Based on the presentation by Kraus, Forsburg and Xu
-- https://arxiv.org/abs/2104.02549

-- The main difference is that we allow the limit over the elements of any code type, not just natural numbers

--TODO: don't make ℓ module param
module CodeSize {{æ : Æ}} {{_ : Datatypes}} {{_ : DataGermCodes}} where

open import Code
-- open import Head
open import Util

-- QIIT Brouwer trees, from Kraus et al https://arxiv.org/pdf/2104.02549.pdf
data Ord : Set where
  OZ : Ord
  O↑ : Ord -> Ord
  OLim : ∀ {ℓ} (c : ℂ ℓ) → (f : El c → Ord) → Ord
  -- OBisim : ∀ {ℓ} {c : ℂ ℓ} → (f g : El c → Ord) → {!!} → OLim c f ≡ OLim c g


data _≤o_ : Ord → Ord → Set where
  ≤o-Z : ∀ {o} → OZ ≤o o
  ≤o-sucMono : ∀ {o1 o2} → o1 ≤o o2 → O↑ o1 ≤o O↑ o2
  ≤o-cocone : ∀ {o ℓ} {c : ℂ ℓ} (f : El c → Ord) (k : El c) → o ≤o f k → o ≤o OLim c f
  ≤o-limiting : ∀ {o ℓ} {c : ℂ ℓ} → (f : El c → Ord) → (∀ k → f k ≤o o) → OLim c f ≤o o

≤o-refl : ∀ o → o ≤o o
≤o-refl OZ = ≤o-Z
≤o-refl (O↑ o) = ≤o-sucMono (≤o-refl o)
≤o-refl (OLim c f) = ≤o-limiting f (λ k → ≤o-cocone f k (≤o-refl (f k)))


≤o-trans : ∀ {o1 o2 o3} → o1 ≤o o2 → o2 ≤o o3 → o1 ≤o o3
≤o-trans ≤o-Z p23 = ≤o-Z
≤o-trans (≤o-sucMono p12) (≤o-sucMono p23) = ≤o-sucMono (≤o-trans p12 p23)
≤o-trans p12 (≤o-cocone f k p23) = ≤o-cocone f k (≤o-trans p12 p23)
≤o-trans (≤o-limiting f x) p23 = ≤o-limiting f (λ k → ≤o-trans (x k) p23)
≤o-trans (≤o-cocone f k p12) (≤o-limiting .f x) = ≤o-trans p12 (x k)

_<o_ : Ord → Ord → Set
o1 <o o2 = O↑ o1 ≤o o2

≤↑ : ∀ o → o ≤o O↑ o
≤↑ OZ = ≤o-Z
≤↑ (O↑ o) = ≤o-sucMono (≤↑ o)
≤↑ (OLim c f) = ≤o-limiting f λ k → ≤o-trans (≤↑ (f k)) (≤o-sucMono (≤o-cocone f k (≤o-refl (f k))))


<-in-≤ : ∀ {x y} → x <o y → x ≤o y
<-in-≤ pf = ≤o-trans (≤↑ _) pf

-- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
-- TODO: proper credit
<∘≤-in-< : ∀ {x y z} → x <o y → y ≤o z → x <o z
<∘≤-in-< x<y y≤z = ≤o-trans x<y y≤z

-- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
-- TODO: proper credit
≤∘<-in-< : ∀ {x y z} → x ≤o y → y <o z → x <o z
≤∘<-in-< {x} {y} {z} x≤y y<z = ≤o-trans (≤o-sucMono x≤y) y<z

underLim : ∀ {ℓ} {c : ℂ ℓ} o →  (f : El c → Ord) → (∀ k → o ≤o f k) → o ≤o OLim c f
underLim {c = c} o f all = ≤o-trans (≤o-cocone {c = c} (λ _ → o) (℧ c) (≤o-refl o)) (≤o-limiting (λ _ → o) (λ k → ≤o-cocone f k (all k)))

extLim : ∀ {ℓ} {c : ℂ ℓ} →  (f1 f2 : El c → Ord) → (∀ k → f1 k ≤o f2 k) → OLim c f1 ≤o OLim c f2
extLim {c = c} f1 f2 all = ≤o-limiting f1 (λ k → ≤o-cocone f2 k (all k))

¬Z<↑ : ∀  o → ¬ ((O↑ o) ≤o OZ)
¬Z<↑ o ()

-- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
-- TODO: proper credit
smaller-accessible : (x : Ord) → Acc _<o_ x → ∀ y → y ≤o x → Acc _<o_ y
smaller-accessible x isAcc y x<y = acc (λ y' y'<y → access isAcc y' (<∘≤-in-< y'<y x<y))

-- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
-- TODO: proper credit
ordWF : WellFounded _<o_
ordWF OZ = acc λ _ ()
ordWF (O↑ x) = acc (λ { y (≤o-sucMono y≤x) → smaller-accessible x (ordWF x) y y≤x})
ordWF (OLim c f) = acc helper
  where
    helper : (y : Ord) → (y <o OLim c f) → Acc _<o_ y
    helper y (≤o-cocone .f k y<fk) = smaller-accessible (f k) (ordWF (f k)) y (<-in-≤ y<fk)

data _<oo_ : (Ord × Ord) → (Ord × Ord) → Set where
  <ooL : ∀ {o1 o2 o1' o2'} → o1 <o o2 → (o1 , o1') <oo (o2 , o2')
  <ooR : ∀ {o1 o2 o1' o2'} → o1 ≡p o2 → o1' <o o2' → (o1 , o1') <oo (o2 , o2')

≤oo-reflL : ∀ {o o1' o2'} → (o , o1') <oo (O↑ o , o2')
≤oo-reflL = <ooL (≤o-refl _)


≤oo-reflR : ∀ {o o'} → (o , o') <oo (o , O↑ o')
≤oo-reflR = <ooR reflp (≤o-refl _)

≤oo-sucL : ∀ {o1 o2 o1' o2'} → o1 ≤o o2 → (o1 , o1') <oo (O↑ o2 , o2')
≤oo-sucL lt = <ooL (≤o-sucMono lt)

≤oo-sucR : ∀ {o o1' o2'} → o1' ≤o o2' → (o , o1') <oo (o , O↑ o2')
≤oo-sucR lt = <ooR reflp (≤o-sucMono lt)

-- Adapted from https://agda.github.io/agda-stdlib/Data.Product.Relation.Binary.Lex.Strict.html#6731
ordOrdWf : WellFounded _<oo_
ordOrdWf (x1 , x2) = acc (helper (ordWF x1) (ordWF x2))
  where
    helper : ∀ {x1 x2} → Acc _<o_ x1 → Acc _<o_ x2 → WFRec _<oo_ (Acc _<oo_) (x1 , x2)
    helper (acc rec₁) acc₂ (y1 , y2) (<ooL lt) = acc (helper (rec₁ y1 lt) (ordWF y2))
    helper acc₁ (acc rec₂) (y1 , y2) (<ooR reflp lt) = acc (helper acc₁ (rec₂ y2 lt))

abstract
  omax : Ord → Ord → Ord
  omax o1 o2 = OLim {ℓ = 0} C𝟙 λ { false → o1 ; true → o2}


  omax-LUB : ∀ {o1 o2 o} → o1 ≤o o → o2 ≤o o → omax o1 o2 ≤o o
  omax-LUB p1 p2 = ≤o-limiting _ λ { false → p1 ; true → p2}

  omax-≤L : ∀ {o1 o2} → o1 ≤o omax o1 o2
  omax-≤L {o1} {o2} = ≤o-cocone _ false (≤o-refl o1)

  omax-≤R : ∀ {o1 o2} → o2 ≤o omax o1 o2
  omax-≤R {o1} {o2} = ≤o-cocone _ true (≤o-refl o2)

_+o_ : Ord → Ord → Ord
OZ +o o2 = o2
(O↑ o1) +o o2 = O↑ (o1 +o o2)
OLim c f +o OZ = OLim c f
OLim c f +o O↑ o2 = O↑ (OLim c f +o o2)
OLim c f +o OLim c₁ f₁ = OLim c λ a → OLim c₁ λ a₁ → f a +o f₁ a₁
-- -- OLim c (λ x → (f x) +o o2)

+o-≤-L : ∀ o1 o2 → o1 ≤o (o1 +o o2)
+o-≤-L OZ o2 = ≤o-Z
+o-≤-L (O↑ o1) o2 = ≤o-sucMono (+o-≤-L o1 o2)
+o-≤-L (OLim c f) OZ = ≤o-refl _
+o-≤-L (OLim c f) (O↑ o2) = ≤o-trans (+o-≤-L (OLim c f) o2) (≤↑ (OLim c f +o o2))
+o-≤-L (OLim c f) (OLim c₁ f₁) = extLim _ _  λ k → underLim (f k) (λ a₁ → f k +o f₁ a₁) (λ k2 → +o-≤-L (f k) (f₁ k2))

+o-≤-R :  ∀ o1 o2 → o2 ≤o (o1 +o o2)
+o-≤-R OZ o2 = ≤o-refl o2
+o-≤-R (O↑ o1) o2 = ≤o-trans (+o-≤-R o1 o2) (≤↑ (o1 +o o2))
+o-≤-R (OLim c f) OZ = ≤o-Z
+o-≤-R (OLim c f) (O↑ o2) = ≤o-sucMono (+o-≤-R (OLim c f) o2)
+o-≤-R (OLim c f) (OLim c₁ f₁) = ≤o-limiting f₁ (λ k → ≤o-cocone (λ a → OLim c₁ (λ a₁ → f a +o f₁ a₁)) (℧ c) (≤o-cocone (λ a₁ → f (℧ c) +o f₁ a₁) k (+o-≤-R (f (℧ c)) (f₁ k))))



CFin : ∀ (n : ℕ) → ℂ 0
CFin ℕ.zero = C℧
CFin (ℕ.suc n) = CΣ C𝟙 (λ { false → C℧ ; true → CFin n})


fromCFin : ∀ {n} → El (CFin n) → Fin (ℕ.suc n)
fromCFin {ℕ.zero} x = Fin.zero
fromCFin {ℕ.suc n} (false , rest) = Fin.zero
fromCFin {ℕ.suc n} (true , rest) = Fin.suc (fromCFin rest)



O1 = O↑ OZ


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


GermSizeW : ∀ {ℓ} (tyCtor : CName)  → W (germContainer ℓ tyCtor (dfix F⁇)) (⁇Ty ℓ) tt → Ord
TreeSizeW : ∀ {ℓ} (tyCtor : CName)
  → (D : GermDesc)
  → FContainer (interpGerm D) (W (germContainer ℓ tyCtor (dfix F⁇)) (⁇Ty ℓ)) (⁇Ty ℓ) tt
  → DataGermIsCode ℓ D
  → Ord
TreeSizeW tyCtor GEnd (FC com k unk) GEndCode = {!!}
TreeSizeW tyCtor (GArg A x) (FC (a , com) k unk) (GArgCode c x₁ x₂) = O↑ (omax (codeSize c) {!!})
TreeSizeW tyCtor (GArg .(∀ x₄ → _ x₄) x) (FC com k unk) (GGuardedArgCode ca x₁ x₂ x₃) = {!!}
TreeSizeW tyCtor (GHRec A x) (FC com k unk) (GHRecCode c x₁ x₂) = {!!}
TreeSizeW tyCtor (GHRec A x) (FC com k unk) (GGuardedRecCode c x₁ x₂) = {!!}
TreeSizeW tyCtor (GUnk A D) (FC com k unk) (GUnkCode c x pf) = {!!}
TreeSizeW tyCtor (GUnk A D) (FC com k unk) (GGuardedUnkCode c x pf) = {!!}

GermSizeW {ℓ} tyCtor (Wsup (FC (d , c) k unk))
  = O↑ (TreeSizeW tyCtor (dataGerm ℓ tyCtor (dfix F⁇) d) (FC c k unk) (dataGermIsCode ℓ tyCtor d))
GermSizeW tyCtor W℧ = O1
GermSizeW tyCtor W⁇ = O1

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
⁇Size {ℓ = ℓ} (CodeModule.⁇μ tyCtor x) = GermSizeW tyCtor x
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

open import Cubical.Induction.WellFounded


orec : ∀ {ℓ} (P : Ord → Set ℓ)
  → ((x : Ord) → (rec : (y : Ord) → (_ : y <o x) → P y ) → P x)
  → ∀ {o} → P o
orec P f = induction (λ x rec → f x rec) _
  where open WFI (ordWF)


oorec : ∀ {ℓ} (P : Ord → Ord → Set ℓ)
  → ((x1 x2 : Ord) → (rec : (y1 y2 : Ord) → (_ : (y1 , y2) <oo (x1 , x2)) → P y1 y2 ) → P x1 x2)
  → ∀ {o1 o2} → P o1 o2
oorec P f = induction (λ (x1 , x2) rec → f x1 x2 λ y1 y2 → rec (y1 , y2)) _
  where open WFI (ordOrdWf)




℧size : ∀ {ℓ} (c : ℂ ℓ) → elSize c (℧ c) ≤o O1
℧size CodeModule.C⁇ = ≤o-refl _
℧size CodeModule.C℧ = ≤o-refl _
℧size CodeModule.C𝟘 = ≤o-refl _
℧size CodeModule.C𝟙 = ≤o-refl _
℧size {suc ℓ} CodeModule.CType = ≤o-refl _
℧size (CodeModule.CΠ c cod) = ≤o-limiting (λ x → elSize (cod x) (℧ (CΠ c cod) x)) (λ k → ℧size (cod k))
℧size (CodeModule.CΣ c cod) = omax-LUB (℧size c) (℧size (cod _))
℧size (CodeModule.C≡ c x y) = ℧size c
℧size (CodeModule.Cμ tyCtor c D x) = ≤o-refl _

codeSuc : ∀ {ℓ} (c : ℂ ℓ) → Σ[ o ∈ Ord ](codeSize c ≡p O↑ o)
codeSuc CodeModule.C⁇ = _ , reflp
codeSuc CodeModule.C℧ = _ , reflp
codeSuc CodeModule.C𝟘 = _ , reflp
codeSuc CodeModule.C𝟙 = _ , reflp
codeSuc CodeModule.CType = _ , reflp
codeSuc (CodeModule.CΠ c cod) = _ , reflp
codeSuc (CodeModule.CΣ c cod) = _ , reflp
codeSuc (CodeModule.C≡ c x y) = _ , reflp
codeSuc (CodeModule.Cμ tyCtor c D x) with numCtors tyCtor
... | ℕ.zero = _ , reflp
... | ℕ.suc n = _ , reflp

-- elSizeLowerBound : ∀ {ℓ} (c : ℂ ℓ) → (x : El c) → O1 ≤o elSize c x
-- ⁇SizeLowerBound : ∀ {ℓ} (x : ⁇Ty ℓ) → O1 ≤o ⁇Size x
-- codeSizeLowerBound : ∀ {ℓ} (c : ℂ ℓ) → O1 ≤o codeSize c

-- codeSizeLowerBound C⁇ = ≤o-refl _
-- codeSizeLowerBound C℧ = ≤o-refl _
-- codeSizeLowerBound C𝟘 = ≤o-refl _
-- codeSizeLowerBound C𝟙 = ≤o-refl _
-- codeSizeLowerBound CType = ≤o-refl _
-- codeSizeLowerBound (CΠ c cod) = ≤o-sucMono ≤o-Z
-- codeSizeLowerBound (CΣ c cod) = ≤o-sucMono ≤o-Z
-- codeSizeLowerBound (C≡ c x y) = ≤o-sucMono ≤o-Z
-- codeSizeLowerBound (Cμ tyCtor c D x) with numCtors tyCtor
-- ... | ℕ.zero = ≤o-refl _
-- ... | ℕ.suc n = ≤o-sucMono ≤o-Z

-- elSizeLowerBound C⁇ x = ⁇SizeLowerBound x
-- elSizeLowerBound C℧ x = ≤o-refl _
-- elSizeLowerBound C𝟘 x = ≤o-refl _
-- elSizeLowerBound C𝟙 x = ≤o-refl _
-- elSizeLowerBound {suc ℓ} CType x = codeSizeLowerBound x
-- elSizeLowerBound (CΠ dom cod) f = underLim O1 (λ x → elSize (cod x) (f x)) (λ k → elSizeLowerBound (cod k) (f k))
-- elSizeLowerBound (CΣ c cod) (x , y) = ≤o-trans (elSizeLowerBound c x) omax-≤L
-- elSizeLowerBound (C≡ c x₁ y) (x ⊢ _ ≅ _) = elSizeLowerBound c x
-- elSizeLowerBound (CodeModule.Cμ tyCtor c D x₁) (Wsup x) = ≤o-sucMono ≤o-Z
-- elSizeLowerBound (CodeModule.Cμ tyCtor c D x₁) W℧ = ≤o-sucMono ≤o-Z
-- elSizeLowerBound (CodeModule.Cμ tyCtor c D x₁) W⁇ = ≤o-sucMono ≤o-Z

-- ⁇SizeLowerBound CodeModule.⁇⁇ = ≤o-refl _
-- ⁇SizeLowerBound CodeModule.⁇℧ = ≤o-refl _
-- ⁇SizeLowerBound CodeModule.⁇𝟙 = ≤o-refl _
-- ⁇SizeLowerBound {suc ℓ} (CodeModule.⁇Type x) = codeSizeLowerBound x
-- ⁇SizeLowerBound (CodeModule.⁇Π x) = ≤o-sucMono ≤o-Z
-- ⁇SizeLowerBound (CodeModule.⁇Σ x) = ≤o-sucMono ≤o-Z
-- ⁇SizeLowerBound (CodeModule.⁇≡ (x ⊢ _ ≅ _)) = ≤o-sucMono ≤o-Z
-- ⁇SizeLowerBound (CodeModule.⁇μ tyCtor x) = ≤o-sucMono ≤o-Z

oplus-suc-swap : ∀ o1 o2 → ((O↑ o1) +o o2) ≤o (o1 +o (O↑ o2))
oplus-suc-swap OZ o2 = ≤o-refl (O↑ OZ +o o2)
oplus-suc-swap (O↑ o1) o2 = ≤o-sucMono (oplus-suc-swap o1 o2)
oplus-suc-swap (OLim c f) OZ = ≤o-refl _
oplus-suc-swap (OLim c f) (O↑ o2) = ≤o-refl _
oplus-suc-swap (OLim c f) (OLim c₁ f₁) = ≤o-refl _

-- instance
mutual
  LT-refl : ∀ {o} → o <o O↑ o
  LT-refl = ≤o-refl _

  maxLT-L : ∀ {o1 o2} → o1 <o O↑ (omax o1 o2)
  maxLT-L {o1} {o2} = ≤o-sucMono omax-≤L

  maxLT-R : ∀ {o1 o2} → o2 <o O↑ (omax o1 o2)
  maxLT-R {o1} {o2} = ≤o-sucMono omax-≤R

  limLT : ∀ {ℓ} {c : ℂ ℓ} { f x} → f x <o O↑ (OLim c f)
  limLT {c = c} {f} {x} = ≤o-sucMono (≤o-cocone f x (≤o-refl (f x)))

  limMaxLT-R : ∀ {o} {ℓ} {c : ℂ ℓ} {f x}  → f x <o O↑ (omax o (OLim c f))
  limMaxLT-R {f = f} {x = x} = ≤o-sucMono (≤o-trans (≤o-cocone f x (≤o-refl (f x))) omax-≤R)

  maxInLimGen-L : ∀  {ℓ} {c : ℂ ℓ} {f1 f2 : El c → Ord}  → OLim c f1 <o O↑ (OLim c λ a → omax (f1 a) (f2 a))
  maxInLimGen-L {c = c} {f1} {f2} = ≤o-sucMono (extLim f1 (λ a → omax (f1 a) (f2 a)) (λ k → omax-≤L))

  maxInLimGen-R : ∀  {ℓ} {c : ℂ ℓ} {f1 f2 : El c → Ord}  → OLim c f2 <o O↑ (OLim c λ a → omax (f1 a) (f2 a))
  maxInLimGen-R {c = c} {f1} {f2} = ≤o-sucMono (≤o-limiting f2 λ a → (≤o-cocone (λ a₁ → omax (f1 a₁) (f2 a₁)) a omax-≤R))

  maxInLimApp-L : ∀  {ℓ} {c : ℂ ℓ} {f1 f2 : El c → Ord} {x}  → f1 x <o O↑ (OLim c λ a → omax (f1 a) (f2 a))
  maxInLimApp-L {c = c} {f1} {f2} {x} = ≤o-sucMono (≤o-trans (≤o-cocone {c = c} f1 x (≤o-refl (f1 x))) (≤o-limiting f1 (λ a → (≤o-cocone (λ a₁ → omax (f1 a₁) (f2 a₁)) a omax-≤L))))

  maxInLimApp-R : ∀  {ℓ} {c : ℂ ℓ} {f1 f2 : El c → Ord} {x}  → f2 x <o O↑ (OLim c λ a → omax (f1 a) (f2 a))
  maxInLimApp-R {c = c} {f1} {f2} {x} = ≤o-sucMono (≤o-trans (≤o-cocone {c = c} f2 x (≤o-refl (f2 x))) (≤o-limiting f2 (λ a → (≤o-cocone (λ a₁ → omax (f1 a₁) (f2 a₁)) a omax-≤R))))

  onePlusCode-L : ∀ {ℓ} {c1 c2 : ℂ ℓ} → codeSize c1 <o ((codeSize c1) +o (codeSize c2))
  onePlusCode-L {c1 = c1} {c2} with (o1 , pf1) ← codeSuc c1 | (o2 , pf2) ← codeSuc c2 rewrite pf1 rewrite pf2 = ≤o-sucMono (≤o-trans (≤o-sucMono (+o-≤-L o1 o2)) (oplus-suc-swap o1 o2))

  onePlusCode-R : ∀ {ℓ} {c1 c2 : ℂ ℓ} → codeSize c2 <o ((codeSize c1) +o (codeSize c2))
  onePlusCode-R {c1 = c1} {c2} with (o1 , pf1) ← codeSuc c1 | (o2 , pf2) ← codeSuc c2 rewrite pf1 rewrite pf2 = ≤o-sucMono (≤o-trans (≤o-sucMono (+o-≤-R o1 o2)) (oplus-suc-swap o1 o2))
