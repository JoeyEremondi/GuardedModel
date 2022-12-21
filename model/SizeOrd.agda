
{-# OPTIONS --cubical --guarded #-}
-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
-- open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.Data.FinData
-- open import Cubical.Data.Equality
open import Cubical.Data.Sigma
open import UnkGerm
open import GuardedAlgebra
open import Cubical.Induction.WellFounded
open import Cubical.Foundations.Prelude
-- open import Cubical.Data.Equality using (ptoc)
open import Cubical.HITs.PropositionalTruncation as Prop

open import ApproxExact

open import Cubical.Foundations.Transport

module SizeOrd {{_ : DataTypes}} {{_ : DataGerms}} where

open import RawOrd
open import Code


-- We only ever attach a size to the approximate part of a computation
-- and we only need this conversion for making a size
private
  instance
    approxÆ : Æ
    approxÆ = Approx

-- open import Cubical.HITs.PropositionalTruncation as P
-- open import Cubical.HITs.SetQuotients as Q
-- open import Cubical.Foundations.Isomorphism

-- Sizes are like Ords that are well behaved for describing the sizes of terms
-- This whole module is just a way to give a nice abstract interface over what's in Ord


record Size : Set where
  constructor OS
  field
    sOrd : Ord
    sIdem : omax sOrd sOrd ≤o sOrd
open Size

abstract
  smax : Size → Size → Size
  smax s1 s2 = OS (omax (sOrd s1) (sOrd s2)) (omax-swap4 ≤⨟o omax-mono (sIdem s1) (sIdem s2))

  _≤ₛ_ : Size → Size → Set
  _≤ₛ_ s1 s2 = sOrd s1 ≤o sOrd s2


  SZ : Size
  SZ = OS OZ (subst (λ x → x ≤o OZ) (symPath (omax-Z OZ)) ≤o-Z)


  S↑ : Size → Size
  S↑ (OS o pf) = OS (O↑ o) ( subst (λ x → x ≤o O↑ o) (sym omax-↑) (≤o-sucMono pf) )

_<ₛ_ : Size → Size → Set
_<ₛ_ s1 s2 = (S↑ s1) ≤ₛ s2

abstract
  ≤↑ : ∀ s → s ≤ₛ S↑ s
  ≤↑ s =  ≤↑o _


  SLim : ∀  {ℓ} (c : ℂ ℓ) → (f : ApproxEl c → Size) → Size
  SLim c f = OS (omax∞ (OLim c (λ x → sOrd (f x)))) ( omax∞-idem (OLim c (λ x → sOrd (f x))) )


  ≤ₛ-Z : ∀ {s} → SZ ≤ₛ s
  ≤ₛ-Z =  ≤o-Z

  ≤ₛ-sucMono : ∀ {s1 s2} → s1 ≤ₛ s2 → S↑ s1 ≤ₛ S↑ s2
  ≤ₛ-sucMono lt = ≤o-sucMono lt

  infixr 10 _≤⨟_
  _≤⨟_ : ∀ {s1 s2 s3} → s1 ≤ₛ s2 → s2 ≤ₛ s3 → s1 ≤ₛ s3
  _≤⨟_  =  ≤o-trans


  ≤ₛ-refl : ∀ {s} → s ≤ₛ s
  ≤ₛ-refl =  ≤o-refl _

  ≤ₛ-cocone : ∀  {ℓ} {c : ℂ ℓ} → {f : ApproxEl c → Size}
    → ∀ k → f k ≤ₛ SLim c f
  ≤ₛ-cocone {c = c} {f = f} k =  ≤o-cocone (λ x → sOrd (f x)) k (≤o-refl _) ≤⨟o omax∞-self (OLim c (λ x → sOrd (f x)))

  ≤ₛ-limiting : ∀  {ℓ} {c : ℂ ℓ} → {f : ApproxEl c → Size}
    → {s : Size}
    → (∀ k → f k ≤ₛ s) → SLim c f ≤ₛ s
  ≤ₛ-limiting {f = f} {s = OS o idem} lt = ≤o-trans (omax∞-mono (≤o-limiting (λ x → sOrd (f x)) λ k → lt k))  (omax∞-≤ idem)

  ≤ₛ-extLim : ∀ {{æ : Æ}} {ℓ} {c : ℂ ℓ} → {f1 f2 : ApproxEl c → Size}
    → (∀ k → f1 k ≤ₛ f2 k)
    → SLim c f1 ≤ₛ SLim c f2
  ≤ₛ-extLim {f1 = f1} {f2} lt =  omax∞-mono (extLim (λ x → sOrd (f1 x)) (λ x → sOrd (f2 x)) lt)

  ¬Z<↑ : ∀  s → ¬ ((S↑ s) ≤ₛ SZ)
  ¬Z<↑ s = ¬Z<↑o (sOrd s)

  smax-≤L : ∀ {s1 s2} → s1 ≤ₛ smax s1 s2
  smax-≤L =  omax-≤L

  smax-≤R : ∀ {s1 s2} → s2 ≤ₛ smax s1 s2
  smax-≤R =  omax-≤R

  smax-mono : ∀ {s1 s1' s2 s2'} → s1 ≤ₛ s1' → s2 ≤ₛ s2' →
    smax s1 s2 ≤ₛ smax s1' s2'
  smax-mono lt1 lt2 =  omax-mono lt1 lt2

  smax-monoR : ∀ {s1 s2 s2'} → s2 ≤ₛ s2' → smax s1 s2 ≤ₛ smax s1 s2'
  smax-monoR {s1} {s2} {s2'} lt = smax-mono {s1 = s1} {s1' = s1} {s2 = s2} {s2' = s2'} (≤ₛ-refl {s1}) lt

  smax-monoL : ∀ {s1 s1' s2} → s1 ≤ₛ s1' → smax s1 s2 ≤ₛ smax s1' s2
  smax-monoL {s1} {s1'} {s2} lt = smax-mono {s1} {s1'} {s2} {s2} lt (≤ₛ-refl {s2})

  smax-idem : ∀ {s} → smax s s ≤ₛ s
  smax-idem {s = OS o pf} = pf

  smax-commut : ∀ s1 s2 → smax s1 s2 ≤ₛ smax s2 s1
  smax-commut s1 s2 =  omax-commut (sOrd s1) (sOrd s2)

  smax-assocL : ∀ s1 s2 s3 → smax s1 (smax s2 s3) ≤ₛ smax (smax s1 s2) s3
  smax-assocL s1 s2 s3 = omax-assocL _ _ _

  smax-assocR : ∀ s1 s2 s3 →  smax (smax s1 s2) s3 ≤ₛ smax s1 (smax s2 s3)
  smax-assocR s1 s2 s3 = omax-assocR _ _ _

  smax-swap4 : ∀ {s1 s1' s2 s2'} → smax (smax s1 s1') (smax s2 s2') ≤ₛ smax (smax s1 s2) (smax s1' s2')
  smax-swap4 =  omax-swap4

  smax-strictMono : ∀ {s1 s1' s2 s2'} → s1 <ₛ s1' → s2 <ₛ s2' → smax s1 s2 <ₛ smax s1' s2'
  smax-strictMono lt1 lt2 =  omax-strictMono lt1 lt2

  smax-sucMono : ∀ {s1 s2 s1' s2'} → smax s1 s2 ≤ₛ smax s1' s2' → smax s1 s2 <ₛ smax (S↑ s1') (S↑ s2')
  smax-sucMono lt =  omax-sucMono lt


smax-lub : ∀ {s1 s2 s} → s1 ≤ₛ s → s2 ≤ₛ s → smax s1 s2 ≤ₛ s
smax-lub lt1 lt2 = smax-mono lt1 lt2 ≤⨟ smax-idem


S1 : Size
S1 = S↑ SZ

abstract
  smax-oneL : ∀ {s} → smax S1 (S↑ s) ≤ₛ S↑ s
  smax-oneL {s = OS o _} =  omax-oneL

  smax-oneR : ∀ {s} → smax (S↑ s) S1 ≤ₛ S↑ s
  smax-oneR {s = OS o _} =  omax-oneR


-- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
-- TODO: proper credit
≤< : ∀ {x y z} → x ≤ₛ y → y <ₛ z → x <ₛ z
≤< {x} {y} {z} x≤y y<z =  (≤ₛ-sucMono x≤y) ≤⨟ y<z


<≤ : ∀ {x y z} → x <ₛ y → y ≤ₛ z → x <ₛ z
<≤ x<y y≤z = x<y ≤⨟  y≤z

<-in-≤ : ∀ {s1 s2} → s1 <ₛ s2 → s1 ≤ₛ s2
<-in-≤ lt = ≤↑ _ ≤⨟ lt

<ₛ-trans : ∀ {s1 s2 s3} → s1 <ₛ s2 → s2 <ₛ s3 → s1 <ₛ s3
<ₛ-trans lt1 lt2 = <≤ lt1 (<-in-≤ lt2)




smax-lim2L :
    ∀
    {ℓ1 ℓ2}
    {c1 : ℂ ℓ1}
    (f1 : ApproxEl  c1 → Size)
    {c2 : ℂ ℓ2}
    (f2 : ApproxEl  c2 → Size)
    → SLim  c1 (λ k1 → SLim  c2 (λ k2 → smax (f1 k1) (f2 k2))) ≤ₛ smax (SLim  c1 f1) (SLim  c2 f2)
smax-lim2L {c1 = c1} f1 {c2 = c2} f2 = ≤ₛ-limiting  (λ k1 → ≤ₛ-limiting  (λ k2 → smax-mono (≤ₛ-cocone  k1) (≤ₛ-cocone  k2)))


data _<ₛPair_ : (Size × Size) → (Size × Size) → Set where
  <ₛPairL : ∀ {o1c o2c o1v o2v} → ∥ o1c <ₛ o2c ∥₁ → (o1c , o1v) <ₛPair (o2c , o2v)
  <ₛPairR : ∀ {o1c o2c o1v o2v} → o1c ≡p o2c → ∥ o1v <ₛ o2v ∥₁ → (o1c , o1v) <ₛPair (o2c , o2v)

≤suc : ∀ {s1 s2} → s1 ≤ₛ s2 → s1 ≤ₛ S↑ s2
≤suc {s1 = s1} lt = ≤↑ s1 ≤⨟ ≤ₛ-sucMono lt

abstract
  sizeWF : WellFounded _<ₛ_
  sizeWF s = sizeAcc (ordWF (sOrd s))
    where
      sizeAcc : ∀ {s} → Acc _<o_ (sOrd s) → Acc _<ₛ_ s
      sizeAcc {s} (acc x) = acc (λ y lt → sizeAcc (x (sOrd y) lt))

  sizeWFAcc : ∀ x → Acc _<ₛ_ x → Acc (λ x y → ∥ x <ₛ y ∥₁) x
  sizeWFAcc x (acc f) = acc λ y → Prop.elim (λ _ → isPropAcc _) λ lt' → sizeWFAcc y (f y lt')

  sizeWFProp : WellFounded (λ x y → ∥ x <ₛ y ∥₁)
  sizeWFProp x = sizeWFAcc x (sizeWF x)

  sizeSquash : ∀ {x y} (p1 p2 : ∥ x <ₛ y ∥₁) → p1 ≡ p2
  sizeSquash = Prop.squash₁


  <ₛPairWF : WellFounded _<ₛPair_
  <ₛPairWF (x1 , x2) = acc (helper (sizeWFProp x1) (sizeWFProp x2))
    where
      helper : ∀ {x1 x2} → Acc (λ v v₁ → ∥ v <ₛ v₁ ∥₁) x1 → Acc (λ v v₁ → ∥ v <ₛ v₁ ∥₁) x2 → WFRec _<ₛPair_ (Acc _<ₛPair_) (x1 , x2)
      helper (acc rec₁) acc₂ (y1 , y2) (<ₛPairL lt) = acc (helper (rec₁ y1 lt ) (sizeWFProp y2))
      helper acc₁ (acc rec₂) (y1 , y2) (<ₛPairR reflp lt) = acc (helper acc₁ (rec₂ y2 lt))



ℕLim : (ℕ → Size) → Size
ℕLim f = SLim (Cℕ {ℓ = 0}) (λ n → f (CℕtoNat n))


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
