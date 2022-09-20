
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
  smax (OS o1 pf1) (OS o2 pf2) = OS (omax o1 o2) (P.rec2 squash (λ lt1 lt2 → ∣ omax-swap4 ≤⨟ omax-mono lt1 lt2 ∣) pf1 pf2)

  _≤ₛ_ : Size → Size → Set
  _≤ₛ_ (OS o1 pf1) (OS o2 pf2) = ∥ o1 ≤o o2 ∥

  SZ : Size
  SZ = OS OZ ∣ subst (λ x → x ≤o OZ) (sym (omax-Z OZ)) ≤o-Z ∣

  S↑ : Size → Size
  S↑ (OS o pf) = OS (O↑ o) (P.rec squash (λ lt → ∣ subst (λ x → x ≤o O↑ o) (sym omax-↑) (≤o-sucMono lt) ∣) pf)

  SLim : ∀ {{æ : Æ}} {ℓ} (c : ℂ ℓ) → (f : Approxed (λ {{æ : Æ}} → El {{æ = æ}} c) → Size) → Size
  SLim c f = OS (omax∞ (OLim c (λ x → sOrd (f x)))) ∣ omax∞-idem (OLim c (λ x → sOrd (f x))) ∣


  ≤ₛ-Z : ∀ {s} → SZ ≤ₛ s
  ≤ₛ-Z = ∣ ≤o-Z ∣

  ≤ₛ-sucMono : ∀ {s1 s2} → s1 ≤ₛ s2 → S↑ s1 ≤ₛ S↑ s2
  ≤ₛ-sucMono lt = P.rec squash (λ lt → ∣ ≤o-sucMono lt ∣) lt

  ≤ₛ-trans : ∀ {s1 s2 s3} → s1 ≤ₛ s2 → s2 ≤ₛ s3 → s1 ≤ₛ s3
  ≤ₛ-trans lt1 lt2 = P.rec2 squash (λ lt1 lt2 → ∣ ≤o-trans lt1 lt2 ∣) lt1 lt2

  ≤ₛ-refl : ∀ {s} → s ≤ₛ s
  ≤ₛ-refl = ∣ ≤o-refl _ ∣

  ≤ₛ-cocone : ∀ {{æ : Æ}} {ℓ} {c : ℂ ℓ} → {f : Approxed (λ {{æ : Æ}} → El {{æ = æ}} c) → Size}
    → ∀ k → f k ≤ₛ SLim c f
  ≤ₛ-cocone {c = c} {f = f} k = ∣ ≤o-cocone (λ x → sOrd (f x)) k (≤o-refl _) ≤⨟ omax∞-self (OLim c (λ x → sOrd (f x))) ∣

  smax-mono : ∀ {s1 s2 s1' s2'} → s1 ≤ₛ s1' → s2 ≤ₛ s2' →
    smax s1 s2 ≤ₛ smax s1' s2'
  smax-mono lt1 lt2 = rec2 squash (λ lt1 lt2 → ∣ omax-mono lt1 lt2 ∣) lt1 lt2

  smax-idem : ∀ {s} → smax s s ≤ₛ s
  smax-idem {s = OS o pf} = P.rec squash (λ lt → ∣ lt ∣) pf

  smax-commut : ∀ {s1 s2} → smax s1 s2 ≤ₛ smax s2 s1
  smax-commut {s1 = s1} {s2 = s2} = ∣ omax-commut (sOrd s1) (sOrd s2) ∣
