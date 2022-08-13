{-# OPTIONS --cubical --guarded #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sum
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
module Ord {{_ : DataTypes}} {{_ : DataGerms}} where
open import Code
C𝔹 : ℂ 0
C𝔹 = C𝟙
-- C𝔹Eq : El (C𝔹 ) ≡ Bool
-- C𝔹Eq = refl

data Ord : Set where
  OZ : Ord
  O↑ : Ord -> Ord
  OLim : ∀ {{æ : Æ}} {ℓ} (c : ℂ ℓ) → (f : Approxed (λ {{æ : Æ}} → El {{æ = æ}} c) → Ord) → Ord
  -- OBisim : ∀ {ℓ} {c : ℂ ℓ} → (f g : El c → Ord) → {!!} → OLim c f ≡ OLim c g

O1 = O↑ OZ

-- from Kraus et al https://arxiv.org/pdf/2104.02549.pdf
data _≤o_ : Ord → Ord → Set where
  ≤o-Z : ∀ {o} → OZ ≤o o
  ≤o-sucMono : ∀ {o1 o2} → o1 ≤o o2 → O↑ o1 ≤o O↑ o2
  ≤o-cocone : ∀ {{æ : Æ}} {o ℓ} {c : ℂ ℓ} (f : Approxed (El c) {{æ}} → Ord) (k : Approxed (El c)) → o ≤o f k → o ≤o OLim c f
  ≤o-limiting : ∀  {{æ : Æ }} {o ℓ} {c : ℂ ℓ} → (f : Approxed (El c) → Ord) → (∀ k → f k ≤o o) → OLim c f ≤o o

≤o-refl : ∀ o → o ≤o o
≤o-refl OZ = ≤o-Z
≤o-refl (O↑ o) = ≤o-sucMono (≤o-refl o)
≤o-refl (OLim c f) = ≤o-limiting f (λ k → ≤o-cocone f k (≤o-refl (f k)))

≤o-reflEq : ∀ {o1 o2} → o1 ≡p o2 → o1 ≤o o2
≤o-reflEq reflp = ≤o-refl _

≤o-trans : ∀ {o1 o2 o3} → o1 ≤o o2 → o2 ≤o o3 → o1 ≤o o3
≤o-trans ≤o-Z p23 = ≤o-Z
≤o-trans (≤o-sucMono p12) (≤o-sucMono p23) = ≤o-sucMono (≤o-trans p12 p23)
≤o-trans p12 (≤o-cocone f k p23) = ≤o-cocone f k (≤o-trans p12 p23)
≤o-trans (≤o-limiting f x) p23 = ≤o-limiting f (λ k → ≤o-trans (x k) p23)
≤o-trans (≤o-cocone f k p12) (≤o-limiting .f x) = ≤o-trans p12 (x k)

≤o-℧ :  ∀ {{æ : Æ}} {o ℓ} {c : ℂ ℓ} {f : Approxed (El c) {{æ}} → Ord} → o ≤o f (℧Approxed c) → o ≤o OLim c f
≤o-℧ {c = c} lt = ≤o-cocone _ (℧Approxed c) lt

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

underLim : ∀ {{_ : Æ}} {ℓ} {c : ℂ ℓ} o →  (f : Approxed (El c) → Ord) → (∀ k → o ≤o f k) → o ≤o OLim c f
underLim {c = c} o f all = ≤o-trans (≤o-℧ {c = c} (≤o-refl _)) (≤o-limiting (λ _ → o) (λ k → ≤o-cocone f k (all k)))

extLim : ∀ {{æ : Æ}} {ℓ} {c : ℂ ℓ} →  (f1 f2 : Approxed (El c) → Ord) → (∀ k → f1 k ≤o f2 k) → OLim c f1 ≤o OLim c f2
extLim {c = c} f1 f2 all = ≤o-limiting f1 (λ k → ≤o-cocone f2 k (all k))


existsLim : ∀ {æ1 æ2 : Æ} {ℓ1 ℓ2} {c1 : ℂ ℓ1} {c2 : ℂ ℓ2} →  (f1 : Approxed (El c1) {{æ = æ1}} → Ord) (f2 : Approxed (El c2) {{æ = æ2}} → Ord) → (∀ k1 → Σ[ k2 ∈ Approxed (El c2) {{æ = æ2}} ] f1 k1 ≤o f2 k2) → OLim {{æ = æ1}} c1 f1 ≤o OLim {{æ = æ2}} c2 f2
existsLim {æ1} {æ2} f1 f2 allex = ≤o-limiting {{æ = æ1}} f1 (λ k → ≤o-cocone {{æ = æ2}} f2 (fst (allex k)) (snd (allex k)))


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

-- Lexicographic ordering. We use c and v because this is useful when recursing on the size of a (c)ode
-- and the size of a value of that (c)ode's interpetation
data _<oPair_ : (Ord × Ord) → (Ord × Ord) → Set where
  <oPairL : ∀ {o1c o2c o1v o2v} → o1c <o o2c → (o1c , o1v) <oPair (o2c , o2v)
  <oPairR : ∀ {o1c o2c o1v o2v} → o1c ≡p o2c → o1v <o o2v → (o1c , o1v) <oPair (o2c , o2v)


-- Similar to the above, but there are two codes and two values being compared
data _<oQuad_ : ((Ord × Ord) × (Ord × Ord)) → ((Ord × Ord) × (Ord × Ord)) → Set where
  <oQuadL : ∀ {o1c o2c o1v o2v} → o1c <oPair o2c → (o1c , o1v) <oQuad (o2c , o2v)
  <oQuadR : ∀ {o1c o2c o1v o2v} → o1c ≡p o2c → o1v <oPair o2v → (o1c , o1v) <oQuad (o2c , o2v)

≤oo-reflL : ∀ {o o1' o2'} → (o , o1') <oPair (O↑ o , o2')
≤oo-reflL = <oPairL (≤o-refl _)


≤oo-reflR : ∀ {o o'} → (o , o') <oPair (o , O↑ o')
≤oo-reflR = <oPairR reflp (≤o-refl _)

≤oo-sucL : ∀ {o1 o2 o1' o2'} → o1 ≤o o2 → (o1 , o1') <oPair (O↑ o2 , o2')
≤oo-sucL lt = <oPairL (≤o-sucMono lt)

≤oo-sucR : ∀ {o o1' o2'} → o1' ≤o o2' → (o , o1') <oPair (o , O↑ o2')
≤oo-sucR lt = <oPairR reflp (≤o-sucMono lt)

-- Adapted from https://agda.github.io/agda-stdlib/Data.Product.Relation.Binary.Lex.Strict.html#6731
oPairWF : WellFounded _<oPair_
oPairWF (x1 , x2) = acc (helper (ordWF x1) (ordWF x2))
  where
    helper : ∀ {x1 x2} → Acc _<o_ x1 → Acc _<o_ x2 → WFRec _<oPair_ (Acc _<oPair_) (x1 , x2)
    helper (acc rec₁) acc₂ (y1 , y2) (<oPairL lt) = acc (helper (rec₁ y1 lt) (ordWF y2))
    helper acc₁ (acc rec₂) (y1 , y2) (<oPairR reflp lt) = acc (helper acc₁ (rec₂ y2 lt))


oQuadWF : WellFounded _<oQuad_
oQuadWF (x1 , x2) = acc (helper (oPairWF x1) (oPairWF x2))
  where
    helper : ∀ {x1 x2} → Acc _<oPair_ x1 → Acc _<oPair_ x2 → WFRec _<oQuad_ (Acc _<oQuad_) (x1 , x2)
    helper (acc rec₁) acc₂ (y1 , y2) (<oQuadL lt) = acc (helper (rec₁ y1 lt) (oPairWF y2))
    helper acc₁ (acc rec₂) (y1 , y2) (<oQuadR reflp lt) = acc (helper acc₁ (rec₂ y2 lt))

-- abstract
private
  data MaxView : Ord → Ord → Set where
    MaxZ-L : ∀ {o} → MaxView OZ o
    MaxZ-R : ∀ {o} → MaxView o OZ
    MaxLim-L : ∀ {ℓ} {{_ : Æ}} {o } {c : ℂ ℓ} {f : Approxed (El c) → Ord} → MaxView (OLim c f) o
    MaxLim-R : ∀ {ℓ} {{_ : Æ}} {o } {c : ℂ ℓ} {f : Approxed (El c) → Ord}
      → (∀ {{æ : Æ}} {ℓ'} {c' : ℂ ℓ'} {f' : Approxed (El c') → Ord} → ¬ (o ≡p OLim {{æ = æ}} c' f'))
      → MaxView o (OLim c f)
    MaxLim-Suc : ∀  {o1 o2 } → MaxView (O↑ o1) (O↑ o2)

  maxView : ∀ o1 o2 → MaxView o1 o2
  maxView OZ o2 = MaxZ-L
  maxView (OLim c f) o2 = MaxLim-L
  maxView (O↑ o1) OZ = MaxZ-R
  maxView (O↑ o1) (OLim c f) = MaxLim-R λ ()
  maxView (O↑ o1) (O↑ o2) = MaxLim-Suc

  omax : Ord → Ord → Ord
  omax' : ∀ {o1 o2} → MaxView o1 o2 → Ord

  omax o1 o2 = omax' (maxView o1 o2)

  omax' {.OZ} {o2} MaxZ-L = o2
  omax' {o1} {.OZ} MaxZ-R = o1
  omax' {(OLim c f)} {o2} MaxLim-L = OLim c λ x → omax (f x) o2
  omax' {o1} {(OLim c f)} (MaxLim-R _) = OLim c (λ x → omax o1 (f x))
  omax' {(O↑ o1)} {(O↑ o2)} MaxLim-Suc = O↑ (omax o1 o2)

mutual
  omax-≤L : ∀ {o1 o2} → o1 ≤o omax o1 o2
  omax-≤L {o1} {o2} with maxView o1 o2
  ... | MaxZ-L = ≤o-Z
  ... | MaxZ-R = ≤o-refl _
  ... | MaxLim-L {f = f} = extLim f (λ x → omax (f x) o2) (λ k → omax-≤L)
  ... | MaxLim-R {f = f} _ = underLim o1 (λ x → omax o1 (f x)) (λ k → omax-≤L)
  ... | MaxLim-Suc = ≤o-sucMono omax-≤L


  omax-≤R : ∀ {o1 o2} → o2 ≤o omax o1 o2
  omax-≤R {o1} {o2} with maxView o1 o2
  ... | MaxZ-R = ≤o-Z
  ... | MaxZ-L = ≤o-refl _
  ... | MaxLim-R {f = f} _ = extLim f (λ x → omax o1 (f x)) (λ k → omax-≤R {o1 = o1} {f k})
  ... | MaxLim-L {f = f} = underLim o2 (λ x → omax (f x) o2) (λ k → omax-≤R {o1 = f k} {o2 = o2})
  ... | MaxLim-Suc {o1} {o2} = ≤o-sucMono (omax-≤R {o1 = o1} {o2 = o2})




  omax-monoR : ∀ {o1 o2 o2'} → o2 ≤o o2' → omax o1 o2 ≤o omax o1 o2'
  omax-monoR' : ∀ {o1 o2 o2'} → o2 <o o2' → omax o1 o2 <o omax (O↑ o1) o2'

  omax-monoR {o1} {o2} {o2'} lt with maxView o1 o2 in eq1 | maxView o1 o2' in eq2
  ... | MaxZ-L  | v2  = ≤o-trans lt (≤o-reflEq (pCong omax' eq2))
  ... | MaxZ-R  | v2  = ≤o-trans omax-≤L (≤o-reflEq (pCong omax' eq2))
  ... | MaxLim-L {f = f1} |  MaxLim-L  = extLim _ _ λ k → omax-monoR {o1 = f1 k} lt
  omax-monoR {o1} {(OLim _ f')} {.(OLim _ f)} (≤o-cocone f k lt) | MaxLim-R neq  | MaxLim-R neq'
    = ≤o-limiting (λ x → omax o1 (f' x)) (λ y → ≤o-cocone (λ x → omax o1 (f x)) k (omax-monoR {o1 = o1} {o2 = f' y} (≤o-trans (≤o-cocone _ y (≤o-refl _)) lt)))
  omax-monoR {o1} {.(OLim _ _)} {o2'} (≤o-limiting f x₁) | MaxLim-R x  | v2  =
    ≤o-trans (≤o-limiting (λ x₂ → omax o1 (f x₂)) λ k → omax-monoR {o1 = o1} (x₁ k)) (≤o-reflEq (pCong omax' eq2))
  omax-monoR {(O↑ o1)} {.(O↑ _)} {.(O↑ _)} (≤o-sucMono lt) | MaxLim-Suc  | MaxLim-Suc  = ≤o-sucMono (omax-monoR {o1 = o1} lt)
  omax-monoR {(O↑ o1)} {(O↑ o2)} {(OLim _ f)} (≤o-cocone f k lt) | MaxLim-Suc  | MaxLim-R x
    = ≤o-trans (omax-monoR' {o1 = o1} {o2 = o2} {o2' = f k} lt) (≤o-cocone (λ x₁ → omax (O↑ o1) (f x₁)) k (≤o-refl _)) --omax-monoR' {!lt!}

  omax-monoR' {o1} {o2} {o2'}  (≤o-sucMono lt) = ≤o-sucMono ( (omax-monoR {o1 = o1} lt))
  omax-monoR' {o1} {o2} {.(OLim _ f)} (≤o-cocone f k lt)
    = ≤o-cocone _ k (omax-monoR' {o1 = o1} lt)


  omax-monoL : ∀ {o1 o1' o2} → o1 ≤o o1' → omax o1 o2 ≤o omax o1' o2
  omax-monoL' : ∀ {o1 o1' o2} → o1 <o o1' → omax o1 o2 <o omax o1' (O↑ o2)
  omax-monoL {o1} {o1'} {o2} lt with maxView o1 o2 in eq1 | maxView o1' o2 in eq2
  ... | MaxZ-L | v2 = ≤o-trans (omax-≤R {o1 = o1'}) (≤o-reflEq (pCong omax' eq2))
  ... | MaxZ-R | v2 = ≤o-trans lt (≤o-trans (omax-≤L {o1 = o1'}) (≤o-reflEq (pCong omax' eq2)))
  omax-monoL {.(OLim _ _)} {.(OLim _ f)} {o2} (≤o-cocone f k lt) | MaxLim-L  | MaxLim-L
    = ≤o-cocone (λ x → omax (f x) o2) k (omax-monoL lt)
  omax-monoL {.(OLim _ _)} {o1'} {o2} (≤o-limiting f lt) | MaxLim-L |  v2
    = ≤o-limiting (λ x₁ → omax (f x₁) o2) λ k → ≤o-trans (omax-monoL (lt k)) (≤o-reflEq (pCong omax' eq2))
  omax-monoL {.OZ} {.OZ} {.(OLim _ _)} ≤o-Z | MaxLim-R neq  | MaxZ-L  = ≤o-refl _
  omax-monoL  {.(OLim _ f)} {.OZ} {.(OLim _ _)} (≤o-limiting f x) | MaxLim-R neq | MaxZ-L
    with () ← neq reflp
  omax-monoL {o1} {.(OLim _ _)} {.(OLim _ _)} (≤o-cocone _ k lt) | MaxLim-R {f = f} neq | MaxLim-L {f = f'}
    = ≤o-limiting (λ x → omax o1 (f x)) (λ y → ≤o-cocone (λ x → omax (f' x) (OLim _ _)) k
      (≤o-trans (omax-monoL lt) (omax-monoR {o1 = f' k} (≤o-cocone f y (≤o-refl _)))))
  ... | MaxLim-R neq | MaxLim-R {f = f} neq' = extLim (λ x → omax o1 (f x)) (λ x → omax o1' (f x)) (λ k → omax-monoL lt)
  omax-monoL {.(O↑ _)} {.(O↑ _)} {.(O↑ _)} (≤o-sucMono lt) | MaxLim-Suc  | MaxLim-Suc
    = ≤o-sucMono (omax-monoL lt)
  omax-monoL {.(O↑ _)} {.(OLim _ f)} {.(O↑ _)} (≤o-cocone f k lt) | MaxLim-Suc  | MaxLim-L
    = ≤o-cocone (λ x → omax (f x) (O↑ _)) k (omax-monoL' lt)

  omax-monoL' {o1} {o1'} {o2} lt with maxView o1 o2 in eq1 | maxView o1' o2 in eq2
  omax-monoL' {o1} {.(O↑ _)} {o2} (≤o-sucMono lt) | v1 | v2 = ≤o-sucMono (≤o-trans (≤o-reflEq (pCong omax' (pSym eq1))) (omax-monoL lt))
  omax-monoL' {o1} {.(OLim _ f)} {o2} (≤o-cocone f k lt) | v1 | v2
    = ≤o-cocone _ k (≤o-trans (≤o-sucMono (≤o-reflEq (pCong omax' (pSym eq1)))) (omax-monoL' lt))


  omax-mono : ∀ {o1 o2 o1' o2'} → o1 ≤o o1' → o2 ≤o o2' → omax o1 o2 ≤o omax o1' o2'
  omax-mono {o1' = o1'} lt1 lt2 = ≤o-trans (omax-monoL lt1) (omax-monoR {o1 = o1'} lt2)

  omax-strictMono : ∀ {o1 o2 o1' o2'} → o1 <o o1' → o2 <o o2' → omax o1 o2 <o omax o1' o2'
  omax-strictMono lt1 lt2 = omax-mono lt1 lt2

  omax-Z : ∀ o → omax o OZ ≡c o
  omax-Z OZ = reflc
  omax-Z (O↑ o) = reflc
  omax-Z (OLim c f) = cong (OLim c) (funExt (λ x → omax-Z (f x)))

  omax-≤Z : ∀ o → omax o OZ ≤o o
  omax-≤Z OZ = ≤o-refl _
  omax-≤Z (O↑ o) = ≤o-refl _
  omax-≤Z (OLim c f) = extLim _ _ (λ k → omax-≤Z (f k))

  omax-oneL : ∀ {o} → omax O1 (O↑ o) ≤o O↑ o
  omax-oneL  = ≤o-refl _

  omax-oneR : ∀ {o} → omax (O↑ o) O1 ≤o O↑ o
  omax-oneR {OZ} = ≤o-sucMono (≤o-refl _)
  omax-oneR {O↑ o} = ≤o-sucMono (≤o-refl _)
  omax-oneR {OLim c f} rewrite ctop (omax-Z (OLim c f))= ≤o-refl _


  omax-limR : ∀ {{æ : Æ}} {ℓ} {c : ℂ ℓ} (f : Approxed (λ {{æ : Æ}} → El {{æ = æ}} c) {{æ = æ}} → Ord) o → omax o (OLim c f) ≤o OLim c (λ k → omax o (f k))
  omax-limR f OZ = ≤o-refl _
  omax-limR f (O↑ o) = extLim _ _ λ k → ≤o-refl _
  omax-limR f (OLim c f₁) = ≤o-limiting _ λ k → ≤o-trans (omax-limR f (f₁ k)) (extLim _ _ (λ k2 → omax-monoL {o1 = f₁ k} {o1' = OLim c f₁} {o2 = f k2}  (≤o-cocone _ k (≤o-refl _))))

  omax-commut : ∀ o1 o2 → omax o1 o2 ≤o omax o2 o1
  omax-commut o1 o2 with maxView o1 o2
  ... | MaxZ-L = omax-≤L
  ... | MaxZ-R = ≤o-refl _
  ... | MaxLim-R {f = f} x = extLim _ _ (λ k → omax-commut o1 (f k))
  ... | MaxLim-Suc {o1 = o1} {o2 = o2} = ≤o-sucMono (omax-commut o1 o2)
  ... | MaxLim-L {c = c} {f = f} with maxView o2 o1
  ... | MaxZ-L = extLim _ _ (λ k → subst (λ x → x ≤o f k) (sym (omax-Z (f k))) (≤o-refl _))
  ... | MaxLim-R x = extLim _ _ (λ k → omax-commut (f k) o2)
  ... | MaxLim-L {c = c2} {f = f2} =
    ≤o-trans (extLim _ _ λ k → omax-limR f2 (f k))
    (≤o-trans (≤o-limiting _ (λ k → ≤o-limiting _ λ k2 → ≤o-cocone _ k2 (≤o-cocone _ k (≤o-refl _))))
    (≤o-trans (≤o-refl (OLim c2 λ k2 → OLim c λ k → omax (f k) (f2 k2)))
    (extLim _ _ (λ k2 → ≤o-limiting _ λ k1 → ≤o-trans (omax-commut (f k1) (f2 k2)) (omax-monoR {o1 = f2 k2} {o2 = f k1} {o2' = OLim c f} (≤o-cocone _ k1 (≤o-refl _)))))))


  omax-assocL : ∀ o1 o2 o3 → omax o1 (omax o2 o3) ≤o omax (omax o1 o2) o3
  omax-assocL o1 o2 o3 with maxView o2 o3 in eq23
  ... | MaxZ-L = omax-monoL {o1 = o1} {o1' = omax o1 OZ} {o2 = o3} omax-≤L
  ... | MaxZ-R = omax-≤L
  ... | m with maxView o1 o2
  ... | MaxZ-L rewrite pSym eq23 = ≤o-refl _
  ... | MaxZ-R rewrite pSym eq23 = ≤o-refl _
  ... | MaxLim-R {f = f} x rewrite pSym eq23 = ≤o-trans (omax-limR (λ x → omax (f x) o3) o1) (extLim _ _ λ k → omax-assocL o1 (f k) o3) -- f,omax-limR f o1
  omax-assocL .(O↑ _) .(O↑ _) .OZ | MaxZ-R  | MaxLim-Suc = ≤o-refl _
  omax-assocL o1 o2 .(OLim _ _) | MaxLim-R {f = f} x   | MaxLim-Suc = extLim _ _ λ k → omax-assocL o1 o2 (f k)
  omax-assocL (O↑ o1) (O↑ o2) (O↑ o3) | MaxLim-Suc  | MaxLim-Suc = ≤o-sucMono (omax-assocL o1 o2 o3)
  ... | MaxLim-L {f = f} rewrite pSym eq23 = extLim _ _ λ k → omax-assocL (f k) o2 o3


  omax-assocR : ∀ o1 o2 o3 →  omax (omax o1 o2) o3 ≤o omax o1 (omax o2 o3)
  omax-assocR o1 o2 o3 = ≤o-trans (omax-commut (omax o1 o2) o3) (≤o-trans (omax-monoR {o1 = o3} (omax-commut o1 o2))
    (≤o-trans (omax-assocL o3 o2 o1) (≤o-trans (omax-commut (omax o3 o2) o1) (omax-monoR {o1 = o1} (omax-commut o3 o2)))))



-- Monotonicity conditions for limits
-- Since we're working constructively, and with arbitrary codes, not just Nats,
-- we require that there be some element that produces a bigger element
-- for each pair of inputs
--
data MonoOrd : Ord → Set where
  MonoZ : MonoOrd OZ
  MonoSuc : ∀ {o} → MonoOrd o → MonoOrd (O↑ o )
  MonoLim : ∀ {{æ : Æ}} {ℓ} {c : ℂ ℓ} {f : Approxed (El c) {{æ}} → Ord}
    → (monoFun : ∀ {k1 k2} → Σ[ k3 ∈ _ ] (omax (f k1) (f k2) ≤o f k3))
    (monoRest  : ∀ {k} → MonoOrd (f k) )
    → MonoOrd (OLim c f)

-- Omax is idempotent on the subset of ords where all limits are for max-respecting functions
-- Notably, our size computations respect this
omax-idem : ∀{o} → MonoOrd o → omax o o ≤o o
omax-idem MonoZ = ≤o-Z
omax-idem (MonoSuc mo) = ≤o-sucMono (omax-idem mo)
omax-idem (MonoLim {c = c} {f = f} monoFun monoRest) = ≤o-limiting _ (λ k1 → ≤o-trans (omax-limR f (f k1)) (existsLim _ _ (λ k2 → monoFun)))

--Omax is a least-upper bound on the monotone subset of ords
omax-lub : ∀ {o1 o2 o3} → MonoOrd o1 → MonoOrd o2 → MonoOrd o3 →
  o1 ≤o o3 → o2 ≤o o3 → omax o1 o2 ≤o o3
omax-lub {o1 = o1} {o2 = o2} {o3 = o3} mo1 mo2 mo3 lt1 lt2
  = ≤o-trans (omax-mono {o1 = o1} {o2 = o2} (≤o-trans (omax-≤L {o2 = o3}) (≤o-trans (omax-monoL lt1) (omax-idem mo3)))
                                            (≤o-trans (omax-≤L {o2 = o3}) (≤o-trans (omax-monoL lt2) (omax-idem mo3))))
    (omax-idem mo3)

-- Omax preserves limit monotonicity
omax-wf : ∀ {o1 o2} → MonoOrd o1 → MonoOrd o2 → MonoOrd (omax o1 o2)
omax-wf {o1} {o2} mo1 mo2 with maxView o1 o2
... | MaxZ-L = mo2
... | MaxZ-R = mo1
omax-wf {(OLim c f)} {o2} (MonoLim monoFun monoRest) mo2 | MaxLim-L
  = MonoLim
    (λ {k1} {k2} →
      let (k , lt) = monoFun {k1 = k1} {k2 = k2}
      in k ,
      ≤o-trans (omax-assocR (f k1) o2 (omax (f k2) o2))
      (≤o-trans
        (omax-monoR {o1 = f k1}
          (≤o-trans
            (omax-monoR {o1 = o2} {o2 = omax (f k2) o2} (omax-commut ((f k2)) o2))
            (≤o-trans (omax-assocL o2 o2 (f k2))
            (≤o-trans (omax-monoL (omax-idem mo2)) (omax-commut o2 (f k2))))))
      (≤o-trans (omax-assocL (f k1) (f k2) o2) (omax-monoL {o1 = omax (f k1) (f k2)} lt))) )
    λ {k} → omax-wf (monoRest {k = k}) mo2
omax-wf {o1} {(OLim c f)} mo1 (MonoLim monoFun monoRest) | MaxLim-R x
  = MonoLim
    (λ {k1} {k2} →
      let (k , lt) = monoFun {k1 = k1} {k2 = k2}
      in k ,
      ≤o-trans (omax-assocR o1 (f k1) (omax o1 (f k2)))
      (≤o-trans (omax-monoR {o1 = o1}
        (≤o-trans (omax-assocL (f k1) o1 (f k2))
        (≤o-trans (omax-monoL {o1 = omax (f k1) o1} {o2 = f k2} (omax-commut (f k1) o1))
        (omax-assocR o1 (f k1) (f k2)))))
      (≤o-trans (omax-assocL o1 o1 (omax (f k1) (f k2)))
      (≤o-trans (omax-monoL {o1 = omax o1 o1} {o2 = omax (f k1) (f k2)} (omax-idem mo1))
      (omax-monoR {o1 = o1} lt))))
      )
    λ {k} → omax-wf mo1 (monoRest {k = k})
omax-wf {.(O↑ _)} {.(O↑ _)} (MonoSuc mo1) (MonoSuc mo2) | MaxLim-Suc = MonoSuc (omax-wf mo1 mo2)



  -- ... | MaxZ-L | MaxZ-L = ≤o-Z
  -- ... | MaxZ-L | MaxZ-R = ≤o-refl _
  -- ... | MaxZ-R | MaxZ-L = ≤o-refl _
  -- ... | MaxZ-R | MaxZ-R = ≤o-Z
  -- ... | MaxLim-L {o = o} {f = f}  | MaxLim-R _ =  extLim _ _ λ k → omax-commut (f k) o
  -- ... | MaxLim-R {o = o} {f = f} _ | MaxLim-L = extLim _ _ λ k → omax-commut o (f k)
  -- -- ... | MaxLim-Lim {ℓ1 = ℓ1} {ℓ2 = ℓ2} {c1 = c1}  {f1 = f1} {c2 = c2} {f2 = f2} | MaxLim-Lim
  -- --   =  ≤o-limiting2 {ℓ1 = ℓ1} {ℓ2} (λ x y → omax (f1 x) (f2 y)) λ k1 k2 → ≤o-cocone2 {ℓ1 = ℓ2} {ℓ2 = ℓ1} (λ x y → omax (f2 x) (f1 y)) k2 k1 (omax-commut (f1 k1) (f2 k2))
  -- ... | MaxLim-Suc {o1 = o1} {o2 = o2} | MaxLim-Suc = ≤o-sucMono (omax-commut o1 o2)
  -- ... | MaxZ-L | MaxLim-L = {!!}
  -- ... | MaxZ-R | MaxLim-R x = {!!}
  -- ... | MaxLim-L | MaxZ-L = {!!}
  -- ... | MaxLim-L | MaxLim-L = {!!}
  -- ... | MaxLim-R x | MaxZ-R = {!!}
  -- ... | MaxLim-R x | MaxLim-R x₁ = {!!}

  -- omax-LUB : ∀ o1 o2 o → o1 ≤o o → o2 ≤o o → omax o1 o2 ≤o o
  -- omax-LUB o1 o2 o lt1 lt2 with maxView o1 o2
  -- omax-LUB .OZ o2 o lt1 lt2 | MaxZ-L = lt2
  -- omax-LUB o1 .OZ o lt1 lt2 | MaxZ-R = lt1
  -- omax-LUB (OLim c f) o2 o lt1 lt2 | MaxLim-L = {!!}
  -- omax-LUB o1 (OLim c f) o lt1 lt2 | MaxLim-R x = {!!}
  -- omax-LUB .(O↑ _) .(O↑ _) o lt1 lt2 | MaxLim-Suc = {!!}

  -- omax-refl : ∀ {o} → omax o o ≤o o
  -- omax-refl {OZ} = ≤o-Z
  -- omax-refl {O↑ o} = ≤o-sucMono omax-refl
  -- omax-refl {OLim c f} = ≤o-limiting _ λ k → {!!}

  -- omax-commut : ∀ {o1 o2} → omax o1 o2 ≤o omax o2 o1
  -- omax-commut {o1 }{o2} with maxView o1 o2 in eq1 | maxView o2 o1 in eq2
  -- ... | MaxZ-L | v2 = ≤o-trans (omax-≤L {o2 = o1}) (≤o-reflEq (pCong omax' eq2))
  -- ... | MaxZ-R | v2 = ≤o-trans (omax-≤R {o1 = o2}) (≤o-reflEq (pCong omax' eq2))
  -- ... | MaxLim-L {f = f} | MaxZ-L  = extLim _ _ (λ k → omax-commut {o1 = f k}  )
  -- ... | MaxLim-L  | MaxLim-L  = {!!}
  -- ... | MaxLim-L  | MaxLim-R neq  = {!!}
  -- ... | MaxLim-R neq | v2 = {!!}
  -- ... | MaxLim-Suc | v2 = {!!}

-- --   omax : Ord → Ord → Ord
-- --   omax o1 o2 = OLim {{Approx}} {ℓ = 0} C𝔹 λ a → if a then o1 else o2


-- --   omax-LUB : ∀ {o1 o2 o} → o1 ≤o o → o2 ≤o o → omax o1 o2 ≤o o
-- --   omax-LUB {o1} {o2} {o} p1 p2 = ≤o-limiting {{Approx}} _ helper
-- --     where
-- --       helper : (k : Bool) → (if k then o1 else o2) ≤o o
-- --       helper false = p2
-- --       helper true = p1

-- --   omax-≤L : ∀ {o1 o2} → o1 ≤o omax o1 o2
-- --   omax-≤L {o1} {o2}   =
-- --     ≤o-cocone {{Approx}} _ true (≤o-refl _)

-- --   omax-≤R : ∀ {o1 o2} → o2 ≤o omax o1 o2
-- --   omax-≤R {o1} {o2}   =
-- --     ≤o-cocone {{Approx}} _ false (≤o-refl _)

-- --   omax-mono : ∀ {o1 o2 o1' o2'} → o1 ≤o o1' → o2 ≤o o2' → (omax o1 o2) ≤o (omax o1' o2')
-- --   omax-mono lt1 lt2 = omax-LUB (≤o-trans lt1 omax-≤L) (≤o-trans lt2 omax-≤R)

-- --   omax-commut : ∀ {o1 o2} → omax o1 o2 ≤o omax o2 o1
-- --   omax-commut = omax-LUB omax-≤R omax-≤L

-- --   data UBView : Ord → Ord → Set where
-- --     UB-ZL : ∀ o → UBView OZ o
-- --     UB-ZR : ∀ o → UBView o OZ
-- --     UB-SS : ∀ o1 o2 → UBView (O↑ o1) (O↑ o2)
-- --     UB-LimL : ∀ {{æ : Æ}} {ℓ} {c : ℂ ℓ} {f : Approxed (λ {{æ : Æ}} → El {{æ = æ}} c) → Ord} { o1 o2} → (¬ (o1 ≡p OZ)) → (¬ (o2 ≡p OZ)) → ((o1 ≡p OLim c f) ⊎ (o2 ≡p OLim c f)) → UBView o1 o2

-- --   ubView : ∀ o1 o2 → UBView o1 o2
-- --   ubView OZ o2 = UB-ZL o2
-- --   ubView o1 OZ = UB-ZR o1
-- --   ubView (O↑ o1) (O↑ o2) = UB-SS o1 o2
-- --   ubView (O↑ o1) (OLim c f) = UB-LimL (λ ()) (λ ()) (inr reflp)
-- --   ubView (OLim c f) (O↑ o2) = UB-LimL (λ ()) (λ ()) (inl reflp)
-- --   ubView (OLim c f) (OLim c₁ f₁) = UB-LimL (λ ()) (λ ()) (inr reflp)

-- --   -- An upper-bound of any two ordinals
-- --   -- Not a true LUB, but has enough of the properties we need
-- --   ub : Ord → Ord → Ord
-- --   ub o1 o2 with ubView o1 o2
-- --   ... | UB-ZL .o2 = o2
-- --   ... | UB-ZR .o1 = o1
-- --   ... | UB-SS o1 o2 = O↑ (ub o1 o2)
-- --   ... | UB-LimL x x₁ x₂ = omax o1 o2



-- -- _+o_ : Ord → Ord → Ord
-- -- OZ +o o2 = o2
-- -- (O↑ o1) +o o2 = O↑ (o1 +o o2)
-- -- OLim c f +o OZ = OLim c f
-- -- OLim c f +o O↑ o2 = O↑ (OLim c f +o o2)
-- -- OLim c f +o OLim c₁ f₁ = OLim c λ a → OLim c₁ λ a₁ → f a +o f₁ a₁
-- -- -- -- OLim c (λ x → (f x) +o o2)

-- -- +o-≤-L : ∀ o1 o2 → o1 ≤o (o1 +o o2)
-- -- +o-≤-L OZ o2 = ≤o-Z
-- -- +o-≤-L (O↑ o1) o2 = ≤o-sucMono (+o-≤-L o1 o2)
-- -- +o-≤-L (OLim c f) OZ = ≤o-refl _
-- -- +o-≤-L (OLim c f) (O↑ o2) = ≤o-trans (+o-≤-L (OLim c f) o2) (≤↑ (OLim c f +o o2))
-- -- +o-≤-L (OLim c f) (OLim c₁ f₁) = extLim _ _  λ k → underLim (f k) (λ a₁ → f k +o f₁ a₁) (λ k2 → +o-≤-L (f k) (f₁ k2))

-- -- +o-≤-R :  ∀ o1 o2 → o2 ≤o (o1 +o o2)
-- -- +o-≤-R OZ o2 = ≤o-refl o2
-- -- +o-≤-R (O↑ o1) o2 = ≤o-trans (+o-≤-R o1 o2) (≤↑ (o1 +o o2))
-- -- +o-≤-R (OLim c f) OZ = ≤o-Z
-- -- +o-≤-R (OLim c f) (O↑ o2) = ≤o-sucMono (+o-≤-R (OLim c f) o2)
-- -- +o-≤-R (OLim c f) (OLim c₁ f₁) = ≤o-limiting f₁ (λ k → ≤o-℧ {c = c} (≤o-cocone _ k (+o-≤-R (f _) (f₁ k))))




open import Cubical.Induction.WellFounded


orec : ∀ {ℓ} (P : Ord → Set ℓ)
  → ((x : Ord) → (rec : (y : Ord) → (_ : y <o x) → P y ) → P x)
  → ∀ {o} → P o
orec P f = induction (λ x rec → f x rec) _
  where open WFI (ordWF)


oPairRec : ∀ {ℓ} (P : Ord → Ord → Set ℓ)
  → ((x1 x2 : Ord) → (rec : (y1 y2 : Ord) → (_ : (y1 , y2) <oPair (x1 , x2)) → P y1 y2 ) → P x1 x2)
  → ∀ {o1 o2} → P o1 o2
oPairRec P f = induction (λ (x1 , x2) rec → f x1 x2 λ y1 y2 → rec (y1 , y2)) _
  where open WFI (oPairWF)


oQuadRec : ∀ {ℓ} (P : (Ord × Ord) → (Ord × Ord) → Set ℓ)
  → ((x1 x2 : Ord × Ord) → (rec : (y1 y2 : Ord × Ord) → (_ : (y1 , y2) <oQuad (x1 , x2)) → P y1 y2 ) → P x1 x2)
  → ∀ {o1 o2} → P o1 o2
oQuadRec P f = induction (λ (x1 , x2) rec → f x1 x2 λ y1 y2 → rec (y1 , y2)) _
  where open WFI (oQuadWF)

-- oplus-suc-swap : ∀ o1 o2 → ((O↑ o1) +o o2) ≤o (o1 +o (O↑ o2))
-- oplus-suc-swap OZ o2 = ≤o-refl (O↑ OZ +o o2)
-- oplus-suc-swap (O↑ o1) o2 = ≤o-sucMono (oplus-suc-swap o1 o2)
-- oplus-suc-swap (OLim c f) OZ = ≤o-refl _
-- oplus-suc-swap (OLim c f) (O↑ o2) = ≤o-refl _
-- oplus-suc-swap (OLim c f) (OLim c₁ f₁) = ≤o-refl _












-- LT-refl : ∀ {o} → o <o O↑ o
-- LT-refl = ≤o-refl _

-- maxLT-L : ∀ {o1 o2} → o1 <o O↑ (omax o1 o2)
-- maxLT-L {o1} {o2} = ≤o-sucMono omax-≤L

-- maxLT-R : ∀ {o1 o2} → o2 <o O↑ (omax o1 o2)
-- maxLT-R {o1} {o2} = ≤o-sucMono omax-≤R

-- limLT : ∀ {{_ : Æ}} {ℓ} {c : ℂ ℓ}  {f : Approxed (El c) → Ord} { x} → f x <o O↑ (OLim c f)
-- limLT {c = c} {f} {x} = ≤o-sucMono (≤o-cocone f x (≤o-refl (f x)))

-- limMaxLT-R : ∀ {{_ : Æ}} {o} {ℓ} {c : ℂ ℓ} {f : Approxed (El c) → Ord} { x} → f x <o O↑ (omax o (OLim c f))
-- limMaxLT-R {f = f} {x = x} = ≤o-sucMono (≤o-trans (≤o-cocone f x (≤o-refl (f x))) omax-≤R)

-- maxInLimGen-L : ∀ {{_ : Æ}} {ℓ} {c : ℂ ℓ} {f1 f2 : Approxed (El c) → Ord}  → OLim c f1 <o O↑ (OLim c λ a → omax (f1 a) (f2 a))
-- maxInLimGen-L {c = c} {f1} {f2} = ≤o-sucMono (extLim f1 (λ a → omax (f1 a) (f2 a)) (λ k → omax-≤L))

-- maxInLimGen-R : ∀ {{_ : Æ}} {ℓ} {c : ℂ ℓ} {f1 f2 : Approxed (El c) → Ord}  → OLim c f2 <o O↑ (OLim c λ a → omax (f1 a) (f2 a))
-- maxInLimGen-R {c = c} {f1} {f2} = ≤o-sucMono (≤o-limiting f2 λ a → (≤o-cocone (λ a₁ → omax (f1 a₁) (f2 a₁)) a omax-≤R))

-- maxInLimApp-L : ∀ {{_ : Æ}} {ℓ} {c : ℂ ℓ} {f1 f2 : Approxed (El c) → Ord} {x}  → f1 x <o O↑ (OLim c λ a → omax (f1 a) (f2 a))
-- maxInLimApp-L {c = c} {f1} {f2} {x} = ≤o-sucMono (≤o-trans (≤o-cocone {c = c} f1 x (≤o-refl (f1 x))) (≤o-limiting f1 (λ a → (≤o-cocone (λ a₁ → omax (f1 a₁) (f2 a₁)) a omax-≤L))))

-- maxInLimApp-R : ∀ {{_ : Æ}} {ℓ} {c : ℂ ℓ} {f1 f2 : Approxed (El c) → Ord} {x}  → f2 x <o O↑ (OLim c λ a → omax (f1 a) (f2 a))
-- maxInLimApp-R {c = c} {f1} {f2} {x} = ≤o-sucMono (≤o-trans (≤o-cocone {c = c} f2 x (≤o-refl (f2 x))) (≤o-limiting f2 (λ a → (≤o-cocone (λ a₁ → omax (f1 a₁) (f2 a₁)) a omax-≤R))))
