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

open import Cubical.Foundations.Transport

-- Brouwer Tree ordinals
-- Based on the presentation by Kraus, Forsburg and Xu
-- https://arxiv.org/abs/2104.02549

-- The main difference is that we allow the limit over the elements of any code type, not just natural numbers

--TODO: don't make ℓ module param
-- module Ord (ℂ : ℕ → Set) (El : ∀ {ℓ} → ℂ ℓ → Set) (℧ : ∀ {ℓ} → (c : ℂ ℓ ) → El c)
--   (C𝔹 : ∀ {ℓ} → ℂ ℓ) (C𝔹Eq : El C𝔹 ≡ Bool) where
module Ord {{ _ : Æ }} {{_ : Datatypes}} where
open import Code
C𝔹 : ℂ 0
C𝔹 = C𝟙
C𝔹Eq : El (C𝔹 ) ≡ Bool
C𝔹Eq = refl

data Ord : Set where
  OZ : Ord
  O↑ : Ord -> Ord
  OLim : ∀ {ℓ} (c : ℂ ℓ) → (f : El c → Ord) → Ord
  -- OBisim : ∀ {ℓ} {c : ℂ ℓ} → (f g : El c → Ord) → {!!} → OLim c f ≡ OLim c g

O1 = O↑ OZ

-- from Kraus et al https://arxiv.org/pdf/2104.02549.pdf
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
  omax o1 o2 = OLim {ℓ = 0} C𝔹 λ a → if transport C𝔹Eq a then o1 else o2


  omax-LUB : ∀ {o1 o2 o} → o1 ≤o o → o2 ≤o o → omax o1 o2 ≤o o
  omax-LUB {o1} {o2} {o} p1 p2 = ≤o-limiting _ helper
    where
      helper : (k : El C𝔹) → (if transport C𝔹Eq k then o1 else o2) ≤o o
      helper k with transport C𝔹Eq k
      ... | true = p1
      ... | false = p2

  omax-≤L : ∀ {o1 o2} → o1 ≤o omax o1 o2
  omax-≤L {o1} {o2} =
    ≤o-cocone _ (transport⁻ C𝔹Eq true)
      (subst (λ x → o1 ≤o (if x then o1 else o2)) (sym (transportTransport⁻ C𝔹Eq true)) (≤o-refl _))

  omax-≤R : ∀ {o1 o2} → o2 ≤o omax o1 o2
  omax-≤R {o1} {o2} =
    ≤o-cocone _ (transport⁻ C𝔹Eq false)
      (subst (λ x → o2 ≤o (if x then o1 else o2)) (sym (transportTransport⁻ C𝔹Eq false)) (≤o-refl _))

  omax-mono : ∀ {o1 o2 o1' o2'} → o1 ≤o o1' → o2 ≤o o2' → (omax o1 o2) ≤o (omax o1' o2')
  omax-mono lt1 lt2 = omax-LUB (≤o-trans lt1 omax-≤L) (≤o-trans lt2 omax-≤R)

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



oplus-suc-swap : ∀ o1 o2 → ((O↑ o1) +o o2) ≤o (o1 +o (O↑ o2))
oplus-suc-swap OZ o2 = ≤o-refl (O↑ OZ +o o2)
oplus-suc-swap (O↑ o1) o2 = ≤o-sucMono (oplus-suc-swap o1 o2)
oplus-suc-swap (OLim c f) OZ = ≤o-refl _
oplus-suc-swap (OLim c f) (O↑ o2) = ≤o-refl _
oplus-suc-swap (OLim c f) (OLim c₁ f₁) = ≤o-refl _

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