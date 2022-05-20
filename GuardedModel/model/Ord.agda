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
  -- "Parallel composition" of ords i.e. injective, monotone pairs
  _|O|_ : Ord → Ord → Ord
  -- OBisim : ∀ {ℓ} {c : ℂ ℓ} → (f g : El c → Ord) → {!!} → OLim c f ≡ OLim c g

O1 = O↑ OZ

data IsSucO : Ord → Set where
  instance isSucO : ∀ {o} → IsSucO (O↑ o)


-- from Kraus et al https://arxiv.org/pdf/2104.02549.pdf
data _≤o_ : Ord → Ord → Set where
  ≤o-Z : ∀ {o} → OZ ≤o o
  ≤o-sucMono : ∀ {o1 o2} → o1 ≤o o2 → O↑ o1 ≤o O↑ o2
  ≤o-cocone : ∀ {{æ : Æ}} {o ℓ} {c : ℂ ℓ} (f : Approxed (El c) {{æ}} → Ord) (k : Approxed (El c)) → o ≤o f k → o ≤o OLim c f
  ≤o-limiting : ∀  {{æ : Æ }} {o ℓ} {c : ℂ ℓ} → (f : Approxed (El c) → Ord) → (∀ k → f k ≤o o) → OLim c f ≤o o
  ≤o-parL : ∀ {o o1 o2} → o ≤o o1 → o ≤o (o1 |O| o2)
  ≤o-parR : ∀ {o o1 o2} → o ≤o o2 → o ≤o (o1 |O| o2)
  ≤o-parMono : ∀ {o1 o2 o1' o2'} → o1 ≤o o1' → o2 ≤o o2' → (o1 |O| o2) ≤o (o1' |O| o2')
  -- ≤o-parStrict : ∀ {o1 o2 o1' o2'} → O↑ o1 ≤o o1' → O↑ o2 ≤o o2' → O↑ (o1 |O| o2) ≤o (o1' |O| o2')


O1≤ : ∀ {o} → {{_ : IsSucO o}} → O1 ≤o o
O1≤ {{isSucO}} = ≤o-sucMono ≤o-Z

≤o-refl : ∀ o → o ≤o o
≤o-refl OZ = ≤o-Z
≤o-refl (O↑ o) = ≤o-sucMono (≤o-refl o)
≤o-refl (OLim c f) = ≤o-limiting f (λ k → ≤o-cocone f k (≤o-refl (f k)))
≤o-refl (o1 |O| o2) = ≤o-parMono (≤o-refl o1) (≤o-refl o2)


≤o-trans : ∀ {o1 o2 o3} → o1 ≤o o2 → o2 ≤o o3 → o1 ≤o o3
≤o-trans ≤o-Z p23 = ≤o-Z
≤o-trans (≤o-sucMono p12) (≤o-sucMono p23) = ≤o-sucMono (≤o-trans p12 p23)
≤o-trans p12 (≤o-cocone f k p23) = ≤o-cocone f k (≤o-trans p12 p23)
≤o-trans (≤o-limiting f x) p23 = ≤o-limiting f (λ k → ≤o-trans (x k) p23)
≤o-trans (≤o-cocone f k p12) (≤o-limiting .f x) = ≤o-trans p12 (x k)
≤o-trans p12 (≤o-parL p23) = ≤o-parL (≤o-trans p12 p23)
≤o-trans p12 (≤o-parR p23) = ≤o-parR (≤o-trans p12 p23)
≤o-trans (≤o-parL p12) (≤o-parMono p23 p23') = ≤o-trans p12 (≤o-parL p23)
≤o-trans (≤o-parR p12) (≤o-parMono p23 p23') = ≤o-trans p12 (≤o-parR p23')
≤o-trans (≤o-parMono p12 p12') (≤o-parMono p23 p23') = ≤o-parMono (≤o-trans p12 p23) (≤o-trans p12' p23')


≤o-℧ :  ∀ {{æ : Æ}} {o ℓ} {c : ℂ ℓ} {f : Approxed (El c) {{æ}} → Ord} → o ≤o f (℧Approxed c) → o ≤o OLim c f
≤o-℧ {c = c} lt = ≤o-cocone _ (℧Approxed c) lt

data _<o_ : Ord → Ord → Set where
  <↑ : ∀ {o1 o2} → O↑ o1 ≤o o2 → o1 <o o2
  <ParL : ∀ {oLow o1 o2 oHigh} → oLow ≤o o1 → (o1 |O| o2) ≤o oHigh → oLow <o oHigh


-- _<o_ : Ord → Ord → Set
-- o1 <o o2 = O↑ o1 ≤o o2

-- ≤↑ : ∀ o → o ≤o O↑ o
-- ≤↑ OZ = ≤o-Z
-- ≤↑ (O↑ o) = ≤o-sucMono (≤↑ o)
-- ≤↑ (OLim c f) = ≤o-limiting f λ k → ≤o-trans (≤↑ (f k)) (≤o-sucMono (≤o-cocone f k (≤o-refl (f k))))
-- ≤↑ (o1 |O| o2) = {!!}

<-in-≤ : ∀ {x y} → x <o y → x ≤o y
<-in-≤ (<↑ x) = {!!}
<-in-≤ (<ParL x x₁) = {!!}

-- -- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
-- -- TODO: proper credit
-- <∘≤-in-< : ∀ {x y z} → x <o y → y ≤o z → x <o z
-- <∘≤-in-< x<y y≤z = ≤o-trans x<y y≤z

-- -- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
-- -- TODO: proper credit
-- ≤∘<-in-< : ∀ {x y z} → x ≤o y → y <o z → x <o z
-- ≤∘<-in-< {x} {y} {z} x≤y y<z = ≤o-trans (≤o-sucMono x≤y) y<z

-- underLim : ∀ {{_ : Æ}} {ℓ} {c : ℂ ℓ} o →  (f : Approxed (El c) → Ord) → (∀ k → o ≤o f k) → o ≤o OLim c f
-- underLim {c = c} o f all = ≤o-trans (≤o-℧ {c = c} (≤o-refl _)) (≤o-limiting (λ _ → o) (λ k → ≤o-cocone f k (all k)))

-- extLim : ∀ {{æ : Æ}} {ℓ} {c : ℂ ℓ} →  (f1 f2 : Approxed (El c) → Ord) → (∀ k → f1 k ≤o f2 k) → OLim c f1 ≤o OLim c f2
-- extLim {c = c} f1 f2 all = ≤o-limiting f1 (λ k → ≤o-cocone f2 k (all k))

-- ¬Z<↑ : ∀  o → ¬ ((O↑ o) ≤o OZ)
-- ¬Z<↑ o ()

-- -- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
-- -- TODO: proper credit
-- smaller-accessible : (x : Ord) → Acc _<o_ x → ∀ y → y ≤o x → Acc _<o_ y
-- smaller-accessible x isAcc y x<y = acc (λ y' y'<y → access isAcc y' (<∘≤-in-< y'<y x<y))

-- -- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
-- -- TODO: proper credit
-- ordWF : WellFounded _<o_
-- ordWF OZ = acc λ _ ()
-- ordWF (O↑ x) = acc (λ { y (≤o-sucMono y≤x) → smaller-accessible x (ordWF x) y y≤x})
-- ordWF (OLim c f) = acc helper
--   where
--     helper : (y : Ord) → (y <o OLim c f) → Acc _<o_ y
--     helper y (≤o-cocone .f k y<fk) = smaller-accessible (f k) (ordWF (f k)) y (<-in-≤ y<fk)

-- -- Lexicographic ordering. We use c and v because this is useful when recursing on the size of a (c)ode
-- -- and the size of a value of that (c)ode's interpetation
-- data _<oPair_ : (Ord × Ord) → (Ord × Ord) → Set where
--   <oPairL : ∀ {o1c o2c o1v o2v} → o1c <o o2c → (o1c , o1v) <oPair (o2c , o2v)
--   <oPairR : ∀ {o1c o2c o1v o2v} → o1c ≡p o2c → o1v <o o2v → (o1c , o1v) <oPair (o2c , o2v)


-- -- Similar to the above, but there are two codes and two values being compared
-- data _<oQuad_ : ((Ord × Ord) × (Ord × Ord)) → ((Ord × Ord) × (Ord × Ord)) → Set where
--   <oQuadL : ∀ {o1c o2c o1v o2v} → o1c <oPair o2c → (o1c , o1v) <oQuad (o2c , o2v)
--   <oQuadR : ∀ {o1c o2c o1v o2v} → o1c ≡p o2c → o1v <oPair o2v → (o1c , o1v) <oQuad (o2c , o2v)

-- ≤oo-reflL : ∀ {o o1' o2'} → (o , o1') <oPair (O↑ o , o2')
-- ≤oo-reflL = <oPairL (≤o-refl _)


-- ≤oo-reflR : ∀ {o o'} → (o , o') <oPair (o , O↑ o')
-- ≤oo-reflR = <oPairR reflp (≤o-refl _)

-- ≤oo-sucL : ∀ {o1 o2 o1' o2'} → o1 ≤o o2 → (o1 , o1') <oPair (O↑ o2 , o2')
-- ≤oo-sucL lt = <oPairL (≤o-sucMono lt)

-- ≤oo-sucR : ∀ {o o1' o2'} → o1' ≤o o2' → (o , o1') <oPair (o , O↑ o2')
-- ≤oo-sucR lt = <oPairR reflp (≤o-sucMono lt)

-- -- Adapted from https://agda.github.io/agda-stdlib/Data.Product.Relation.Binary.Lex.Strict.html#6731
-- oPairWF : WellFounded _<oPair_
-- oPairWF (x1 , x2) = acc (helper (ordWF x1) (ordWF x2))
--   where
--     helper : ∀ {x1 x2} → Acc _<o_ x1 → Acc _<o_ x2 → WFRec _<oPair_ (Acc _<oPair_) (x1 , x2)
--     helper (acc rec₁) acc₂ (y1 , y2) (<oPairL lt) = acc (helper (rec₁ y1 lt) (ordWF y2))
--     helper acc₁ (acc rec₂) (y1 , y2) (<oPairR reflp lt) = acc (helper acc₁ (rec₂ y2 lt))


-- oQuadWF : WellFounded _<oQuad_
-- oQuadWF (x1 , x2) = acc (helper (oPairWF x1) (oPairWF x2))
--   where
--     helper : ∀ {x1 x2} → Acc _<oPair_ x1 → Acc _<oPair_ x2 → WFRec _<oQuad_ (Acc _<oQuad_) (x1 , x2)
--     helper (acc rec₁) acc₂ (y1 , y2) (<oQuadL lt) = acc (helper (rec₁ y1 lt) (oPairWF y2))
--     helper acc₁ (acc rec₂) (y1 , y2) (<oQuadR reflp lt) = acc (helper acc₁ (rec₂ y2 lt))

-- abstract
--   omax : Ord → Ord → Ord
--   omax o1 o2 = OLim {{Approx}} {ℓ = 0} C𝔹 λ a → if a then o1 else o2


--   omax-LUB : ∀ {o1 o2 o} → o1 ≤o o → o2 ≤o o → omax o1 o2 ≤o o
--   omax-LUB {o1} {o2} {o} p1 p2 = ≤o-limiting {{Approx}} _ helper
--     where
--       helper : (k : Bool) → (if k then o1 else o2) ≤o o
--       helper false = p2
--       helper true = p1

--   omax-≤L : ∀ {o1 o2} → o1 ≤o omax o1 o2
--   omax-≤L {o1} {o2}   =
--     ≤o-cocone {{Approx}} _ true (≤o-refl _)

--   omax-≤R : ∀ {o1 o2} → o2 ≤o omax o1 o2
--   omax-≤R {o1} {o2}   =
--     ≤o-cocone {{Approx}} _ false (≤o-refl _)

--   omax-mono : ∀ {o1 o2 o1' o2'} → o1 ≤o o1' → o2 ≤o o2' → (omax o1 o2) ≤o (omax o1' o2')
--   omax-mono lt1 lt2 = omax-LUB (≤o-trans lt1 omax-≤L) (≤o-trans lt2 omax-≤R)

--   omax-commut : ∀ {o1 o2} → omax o1 o2 ≤o omax o2 o1
--   omax-commut = omax-LUB omax-≤R omax-≤L

--   smax : ∀ o1 o2 {{ _ : IsSucO o1}} {{ _ : IsSucO o2 }} → Ord
--   smax (O↑ o1) (O↑ o2) {{isSucO}} {{isSucO}} = O↑ (omax o1 o2)

--   smaxIsSuc : ∀ {o1 o2} {{ _ : IsSucO o1}} {{ _ : IsSucO o2 }} → IsSucO (smax o1 o2)
--   smaxIsSuc {{isSucO}} {{isSucO}} = isSucO

--   smax-LUB : ∀ {o1 o2 o} {{ _ : IsSucO o1}} {{ _ : IsSucO o2 }} {{_ : IsSucO o}}
--     → o1 ≤o o
--     → o2 ≤o o
--     → smax o1 o2 ≤o o
--   smax-LUB {{isSucO}} {{isSucO}} {{isSucO}} (≤o-sucMono lt1) (≤o-sucMono lt2) = ≤o-sucMono (omax-LUB lt1 lt2)

--   smax-≤L : ∀ {o1 o2 } {{ _ : IsSucO o1}} {{ _ : IsSucO o2 }} → o1 ≤o smax o1 o2
--   smax-≤L {{isSucO}} {{isSucO}} = ≤o-sucMono omax-≤L

--   smax-≤R : ∀ {o1 o2 } {{ _ : IsSucO o1}} {{ _ : IsSucO o2 }} → o2 ≤o smax o1 o2
--   smax-≤R {{isSucO}} {{isSucO}} = ≤o-sucMono omax-≤R

--   smax-commut : ∀ {o1 o2 } {{ _ : IsSucO o1}} {{ _ : IsSucO o2 }} → smax o1 o2 ≤o smax o2 o1
--   smax-commut = smax-LUB {{_}} {{_}} {{smaxIsSuc}} smax-≤R smax-≤L


--   data UBView : Ord → Ord → Set where
--     UB-ZL : ∀ o → UBView OZ o
--     UB-ZR : ∀ o → UBView o OZ
--     UB-SS : ∀ o1 o2 → UBView (O↑ o1) (O↑ o2)
--     UB-LimL : ∀ {{æ : Æ}} {ℓ} {c : ℂ ℓ} {f : Approxed (λ {{æ : Æ}} → El {{æ = æ}} c) → Ord} { o1 o2} → (¬ (o1 ≡p OZ)) → (¬ (o2 ≡p OZ)) → ((o1 ≡p OLim c f) ⊎ (o2 ≡p OLim c f)) → UBView o1 o2

--   ubView : ∀ o1 o2 → UBView o1 o2
--   ubView OZ o2 = UB-ZL o2
--   ubView o1 OZ = UB-ZR o1
--   ubView (O↑ o1) (O↑ o2) = UB-SS o1 o2
--   ubView (O↑ o1) (OLim c f) = UB-LimL (λ ()) (λ ()) (inr reflp)
--   ubView (OLim c f) (O↑ o2) = UB-LimL (λ ()) (λ ()) (inl reflp)
--   ubView (OLim c f) (OLim c₁ f₁) = UB-LimL (λ ()) (λ ()) (inr reflp)

--   -- An upper-bound of any two ordinals
--   -- Not a true LUB, but has enough of the properties we need
--   ub : Ord → Ord → Ord
--   ub o1 o2 with ubView o1 o2
--   ... | UB-ZL .o2 = o2
--   ... | UB-ZR .o1 = o1
--   ... | UB-SS o1 o2 = O↑ (ub o1 o2)
--   ... | UB-LimL x x₁ x₂ = omax o1 o2



-- _+o_ : Ord → Ord → Ord
-- OZ +o o2 = o2
-- (O↑ o1) +o o2 = O↑ (o1 +o o2)
-- OLim c f +o OZ = OLim c f
-- OLim c f +o O↑ o2 = O↑ (OLim c f +o o2)
-- OLim c f +o OLim c₁ f₁ = OLim c λ a → OLim c₁ λ a₁ → f a +o f₁ a₁
-- -- -- OLim c (λ x → (f x) +o o2)

-- +o-≤-L : ∀ o1 o2 → o1 ≤o (o1 +o o2)
-- +o-≤-L OZ o2 = ≤o-Z
-- +o-≤-L (O↑ o1) o2 = ≤o-sucMono (+o-≤-L o1 o2)
-- +o-≤-L (OLim c f) OZ = ≤o-refl _
-- +o-≤-L (OLim c f) (O↑ o2) = ≤o-trans (+o-≤-L (OLim c f) o2) (≤↑ (OLim c f +o o2))
-- +o-≤-L (OLim c f) (OLim c₁ f₁) = extLim _ _  λ k → underLim (f k) (λ a₁ → f k +o f₁ a₁) (λ k2 → +o-≤-L (f k) (f₁ k2))

-- +o-≤-R :  ∀ o1 o2 → o2 ≤o (o1 +o o2)
-- +o-≤-R OZ o2 = ≤o-refl o2
-- +o-≤-R (O↑ o1) o2 = ≤o-trans (+o-≤-R o1 o2) (≤↑ (o1 +o o2))
-- +o-≤-R (OLim c f) OZ = ≤o-Z
-- +o-≤-R (OLim c f) (O↑ o2) = ≤o-sucMono (+o-≤-R (OLim c f) o2)
-- +o-≤-R (OLim c f) (OLim c₁ f₁) = ≤o-limiting f₁ (λ k → ≤o-℧ {c = c} (≤o-cocone _ k (+o-≤-R (f _) (f₁ k))))




-- open import Cubical.Induction.WellFounded


-- orec : ∀ {ℓ} (P : Ord → Set ℓ)
--   → ((x : Ord) → (rec : (y : Ord) → (_ : y <o x) → P y ) → P x)
--   → ∀ {o} → P o
-- orec P f = induction (λ x rec → f x rec) _
--   where open WFI (ordWF)


-- oPairRec : ∀ {ℓ} (P : Ord → Ord → Set ℓ)
--   → ((x1 x2 : Ord) → (rec : (y1 y2 : Ord) → (_ : (y1 , y2) <oPair (x1 , x2)) → P y1 y2 ) → P x1 x2)
--   → ∀ {o1 o2} → P o1 o2
-- oPairRec P f = induction (λ (x1 , x2) rec → f x1 x2 λ y1 y2 → rec (y1 , y2)) _
--   where open WFI (oPairWF)


-- oQuadRec : ∀ {ℓ} (P : (Ord × Ord) → (Ord × Ord) → Set ℓ)
--   → ((x1 x2 : Ord × Ord) → (rec : (y1 y2 : Ord × Ord) → (_ : (y1 , y2) <oQuad (x1 , x2)) → P y1 y2 ) → P x1 x2)
--   → ∀ {o1 o2} → P o1 o2
-- oQuadRec P f = induction (λ (x1 , x2) rec → f x1 x2 λ y1 y2 → rec (y1 , y2)) _
--   where open WFI (oQuadWF)

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
