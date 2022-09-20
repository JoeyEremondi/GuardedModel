
{-# OPTIONS --cubical --guarded #-}
-- open import Guarded
open import Cubical.Data.Maybe
open import Cubical.Data.Vec
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

module SizeOrd {{_ : DataTypes}} {{_ : DataGerms}} where

open import Ord
open import Code

open import Cubical.HITs.PropositionalTruncation as P
-- open import Cubical.HITs.SetQuotients as Q
-- open import Cubical.Foundations.Isomorphism

-- Sizes are like Ords that are well behaved for describing the sizes of terms
-- This whole module is just a way to give a nice abstract interface over what's in Ord


record Size : Set where
  constructor OS
  field
    sOrd : Ord
    sIdem : ∥ omax sOrd sOrd ≤o sOrd ∥
open Size

abstract
  smax : Size → Size → Size
  smax s1 s2 = OS (omax (sOrd s1) (sOrd s2)) (P.rec2 squash (λ lt1 lt2 → ∣ omax-swap4 ≤⨟o omax-mono lt1 lt2 ∣) (sIdem s1) (sIdem s2))

  _≤ₛ_ : Size → Size → Set
  _≤ₛ_ s1 s2 = ∥ sOrd s1 ≤o sOrd s2 ∥


  SZ : Size
  SZ = OS OZ ∣ subst (λ x → x ≤o OZ) (sym (omax-Z OZ)) ≤o-Z ∣


  S↑ : Size → Size
  S↑ (OS o pf) = OS (O↑ o) (P.rec squash (λ lt → ∣ subst (λ x → x ≤o O↑ o) (sym omax-↑) (≤o-sucMono lt) ∣) pf)

_<ₛ_ : Size → Size → Set
_<ₛ_ s1 s2 = (S↑ s1) ≤ₛ s2

abstract
  ≤↑ : ∀ s → s ≤ₛ S↑ s
  ≤↑ s = ∣ ≤↑o _ ∣



  SLim : ∀ {{æ : Æ}} {ℓ} (c : ℂ ℓ) → (f : Approxed (λ {{æ : Æ}} → El {{æ = æ}} c) → Size) → Size
  SLim c f = OS (omax∞ (OLim c (λ x → sOrd (f x)))) ∣ omax∞-idem (OLim c (λ x → sOrd (f x))) ∣


  ≤ₛ-Z : ∀ {s} → SZ ≤ₛ s
  ≤ₛ-Z = ∣ ≤o-Z ∣

  ≤ₛ-sucMono : ∀ {s1 s2} → s1 ≤ₛ s2 → S↑ s1 ≤ₛ S↑ s2
  ≤ₛ-sucMono lt = P.rec squash (λ lt → ∣ ≤o-sucMono lt ∣) lt

  infixr 10 _≤⨟_
  _≤⨟_ : ∀ {s1 s2 s3} → s1 ≤ₛ s2 → s2 ≤ₛ s3 → s1 ≤ₛ s3
  _≤⨟_ lt1 lt2 = P.rec2 squash (λ lt1 lt2 → ∣ ≤o-trans lt1 lt2 ∣) lt1 lt2

  ≤ₛ-refl : ∀ {s} → s ≤ₛ s
  ≤ₛ-refl = ∣ ≤o-refl _ ∣

  ≤ₛ-cocone : ∀ {{æ : Æ}} {ℓ} {c : ℂ ℓ} → {f : Approxed (λ {{æ : Æ}} → El {{æ = æ}} c) → Size}
    → ∀ k → f k ≤ₛ SLim c f
  ≤ₛ-cocone {c = c} {f = f} k = ∣ ≤o-cocone (λ x → sOrd (f x)) k (≤o-refl _) ≤⨟o omax∞-self (OLim c (λ x → sOrd (f x))) ∣

  ≤ₛ-extLim : ∀ {{æ : Æ}} {ℓ} {c : ℂ ℓ} → {f1 f2 : Approxed (λ {{æ : Æ}} → El {{æ = æ}} c) → Size}
    → (∀ k → f1 k ≤ₛ f2 k)
    → SLim c f1 ≤ₛ SLim c f2
  ≤ₛ-extLim {f1 = f1} {f2} lt = ∣ omax∞-mono (extLim (λ x → sOrd (f1 x)) (λ x → sOrd (f2 x)) {!!}) ∣


  smax-≤L : ∀ {s1 s2} → s1 ≤ₛ smax s1 s2
  smax-≤L = ∣ omax-≤L ∣

  smax-≤R : ∀ {s1 s2} → s2 ≤ₛ smax s1 s2
  smax-≤R = ∣ omax-≤R ∣

  smax-mono : ∀ {s1 s1' s2 s2'} → s1 ≤ₛ s1' → s2 ≤ₛ s2' →
    smax s1 s2 ≤ₛ smax s1' s2'
  smax-mono lt1 lt2 = rec2 squash (λ lt1 lt2 → ∣ omax-mono lt1 lt2 ∣) lt1 lt2

  smax-monoR : ∀ {s1 s2 s2'} → s2 ≤ₛ s2' → smax s1 s2 ≤ₛ smax s1 s2'
  smax-monoR {s1} {s2} {s2'} lt = smax-mono {s1 = s1} {s1' = s1} {s2 = s2} {s2' = s2'} (≤ₛ-refl {s1}) lt

  smax-monoL : ∀ {s1 s1' s2} → s1 ≤ₛ s1' → smax s1 s2 ≤ₛ smax s1' s2
  smax-monoL {s1} {s1'} {s2} lt = smax-mono {s1} {s1'} {s2} {s2} lt (≤ₛ-refl {s2})

  smax-idem : ∀ {s} → smax s s ≤ₛ s
  smax-idem {s = OS o pf} = P.rec squash (λ lt → ∣ lt ∣) pf

  smax-commut : ∀ {s1 s2} → smax s1 s2 ≤ₛ smax s2 s1
  smax-commut {s1 = s1} {s2 = s2} = ∣ omax-commut (sOrd s1) (sOrd s2) ∣


  smax-swap4 : ∀ {s1 s1' s2 s2'} → smax (smax s1 s1') (smax s2 s2') ≤ₛ smax (smax s1 s2) (smax s1' s2')
  smax-swap4 = ∣ omax-swap4 ∣

  smax-strictMono : ∀ {s1 s1' s2 s2'} → s1 <ₛ s1' → s2 <ₛ s2' → smax s1 s2 <ₛ smax s1' s2'
  smax-strictMono lt1 lt2 = P.rec2 squash (λ lt1 lt2 → ∣ omax-strictMono lt1 lt2 ∣) lt1 lt2

  smax-sucMono : ∀ {s1 s2 s1' s2'} → smax s1 s2 ≤ₛ smax s1' s2' → smax s1 s2 <ₛ smax (S↑ s1') (S↑ s2')
  smax-sucMono lt = P.rec squash (λ lt → ∣ omax-sucMono lt ∣) lt

smax* : ∀ {n} → Vec Size n → Size
smax* [] = SZ
smax* (x ∷ os) = smax x (smax* os)

smax*-≤L : ∀ {n o} {os : Vec Size n} → o ≤ₛ smax* (o ∷ os)
smax*-≤L {o = o} {os = os} = smax-≤L {s1 = o} {s2 = smax* os}

smax*-≤R : ∀ {n o} {os : Vec Size n} → smax* os ≤ₛ smax* (o ∷ os)
smax*-≤R {o = o} {os = os} = smax-≤R {s1 = o} {s2 = smax* os}

smax*-≤-n : ∀ {n} {os : Vec Size n} (f : Fin n) → lookup f os ≤ₛ smax* os
smax*-≤-n {os = o ∷ os} Fin.zero = smax*-≤L {o = o} {os = os}
smax*-≤-n {os = o ∷ os} (Fin.suc f) = smax*-≤-n f ≤⨟ (smax*-≤R {o = o} {os = os})
  -- smax*-≤-n f ≤⨟ (smax*-≤R {o = o} {os = os})

smax*-swap : ∀ {n} {os1 os2 : Vec Size n} → smax* (zipWith smax os1 os2) ≤ₛ smax (smax* os1) (smax* os2)
smax*-swap {n = ℕ.zero} {[]} {[]} = ≤ₛ-Z
smax*-swap {n = ℕ.suc n} {o1 ∷ os1} {o2 ∷ os2} =
  smax-monoR (smax*-swap {n = n}) ≤⨟ smax-swap4
  -- smax-monoR {s1 = smax o1 o2} (smax*-swap {n = n}) ≤⨟ smax-swap4 {o1 = o1} {o1' = o2} {o2 = smax* os1} {o2' = smax* os2}

smax*-mono : ∀ {n} {os1 os2 : Vec Size n} → foldr (λ (o1 , o2) rest → (o1 ≤ₛ o2) × rest) Unit (zipWith _,_ os1 os2) → smax* os1 ≤ₛ smax* os2
smax*-mono {ℕ.zero} {[]} {[]} lt = ≤ₛ-Z
smax*-mono {ℕ.suc n} {o1 ∷ os1} {o2 ∷ os2} (lt , rest) = smax-mono {s1 = o1} {s1' = o2} lt (smax*-mono {os1 = os1} {os2 = os2} rest)

S1 : Size
S1 = S↑ SZ

abstract
  smax-oneL : ∀ {s} → smax S1 (S↑ s) ≤ₛ S↑ s
  smax-oneL {s = OS o _} = ∣ omax-oneL ∣

  smax-oneR : ∀ {s} → smax (S↑ s) S1 ≤ₛ S↑ s
  smax-oneR {s = OS o _} = ∣ omax-oneR ∣
