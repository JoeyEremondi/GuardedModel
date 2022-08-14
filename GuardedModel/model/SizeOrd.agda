
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

-- Sizes are like Ords that are well behaved for describing the sizes of terms
-- This whole module is just a way to give a nice abstract interface over what's in Ord

abstract
  -- The type
  Size : Set
  Size = Σ[ o ∈ Ord ](Σ[ o' ∈ Ord ](o ≡p omax∞ o'))

-- The ordering on sizes
  _≤ₛ_ : Size → Size → Set
  _<ₛ_ : Size → Size → Set

  erase : Size → Ord
  erase = fst



-- The max operation for sizes
  smax : Size → Size → Size



  -- oapp : ∀ {{_ : Æ}} {ℓ} {c : ℂ ℓ} → c →Size → Approxed (λ {{æ : Æ}} → El {{æ = æ}} c) → Ord
  -- oapp f x = fst (sapp f x)


-- Constructors for sizes
  SZ : Size
  S↑ : Size → Size
  SLim :
    ∀ {{æ : Æ}} {ℓ} (c : ℂ ℓ)
    → (f : Approxed (λ {{æ : Æ}} → El {{æ = æ}} c) → Size)
    → Size

-- -- Base Laws for ≤ₛ
  ≤ₛ-Z : ∀ {s} → SZ ≤ₛ s
  ≤ₛ-sucMono : ∀ {s1 s2} → s1 ≤ₛ s2 → S↑ s1 ≤ₛ S↑ s2
  ≤ₛ-cocone : ∀ {{æ : Æ}} {s ℓ} {c : ℂ ℓ}  (f : Approxed (λ {{æ : Æ}} → El {{æ = æ}} c) → Size) k → s ≤ₛ f k → s ≤ₛ SLim c f
  ≤ₛ-limiting : ∀ {{æ : Æ}} {s ℓ} {c : ℂ ℓ}  (f : Approxed (λ {{æ : Æ}} → El {{æ = æ}} c) → Size) → (∀ k → f k ≤ₛ s) → SLim c f ≤ₛ s

  -- <↑s : ∀ {s1 s2} → s1 ≤ₛ s2 → s1 <ₛ S↑ s2

-- -- Derived laws for ≤ₛ
--   ≤ₛ-refl : ∀ {s} → s ≤ₛ s
--   ≤ₛ-trans : ∀ {s1 s2 s3} → s1 ≤ₛ s2 → s2 ≤ₛ s3 → s1 ≤ₛ s3
--   ≤ₛ↑ : ∀ {s} → s ≤ₛ S↑ s

-- -- smax is a LUB
--   smax-≤L : ∀ {s1 s2} → s1 ≤ₛ smax s1 s2
--   smax-≤R : ∀ {s1 s2} → s2 ≤ₛ smax s1 s2
--   smax-LUB : ∀ {s1 s2 s} → s1 ≤ₛ s → s2 ≤ₛ s → smax s1 s2 ≤ₛ s

--   smax-monoL : ∀ {s1 s1' s2} → s1 ≤ₛ s1' → smax s1 s2 ≤ₛ smax s1' s2
--   smax-monoR : ∀ {s1 s2 s2'} → s2 ≤ₛ s2' → smax s1 s2 ≤ₛ smax s1 s2'
--   smax-mono : ∀ {s1 s2 s1' s2'} → s1 ≤ₛ s1' → s2 ≤ₛ s2' → smax s1 s2 ≤ₛ smax s1' s2'
--   smax-assocL : ∀ {s1 s2 s3} → smax s1 (smax s2 s3) ≤ₛ smax (smax s1 s2) s3
--   smax-assocR : ∀ {s1 s2 s3} → smax (smax s1 s2) s3 ≤ₛ smax s1 (smax s2 s3)
--   smax-commut : ∀ {s1 s2} → smax s1 s2 ≤ₛ smax s2 s1

--   smax-strictMono : ∀ {s1 s1' s2 s2'} → s1 <ₛ s1' → s2 <ₛ s2' → smax s1 s2 <ₛ smax s1' s2'

--   -- Well-founded recursion
--   sizeWF : WellFounded _<ₛ_
--   sizeRec : ∀ {ℓ} (P : Size → Set ℓ) → ((sHigh : Size) → ((sLow : Size) → sLow <ₛ sHigh → P sLow) → P sHigh) → ∀ s → P s

--   ----------------------------------------------------------------
--   -- Implementations


  _≤ₛ_ s1 s2 = (fst s1) ≤o (fst s2)

  smax s1 s2 = omax∞ (omax (fst s1) (fst s2)) , _ , reflp

  SZ = (omax∞ OZ , OZ , reflp)

  S↑ (o , o' , pf) = omax∞ (O↑ o) , O↑ o , reflp

  SLim c f = omax∞ (OLim c (λ x → fst (f x))) , OLim c (λ x → fst (f x)) , reflp

  ≤ₛ-Z {s = (_ , s' , reflp)} = omax∞-mono ≤o-Z

  ≤ₛ-sucMono {s1 = _ , s1 , reflp} {s2  = _ , s2 , reflp} lt = omax∞-mono (≤o-sucMono lt)

  ≤ₛ-cocone {s = _ , s , reflp} f k lt = extLim {{æ = Approx}} _ _ λ n → nmax-mono (transport Elℕ n) (≤o-cocone _ k (≤o-trans (omax∞-self s) lt))
--   ≤ₛ-limiting f lt = ≤o-limiting (oapp f) lt
--   ≤ₛ-refl = ≤o-refl _
--   ≤ₛ-trans = ≤o-trans

  _<ₛ_ s1 s2 = S↑ s1 ≤ₛ s2

  _<ₛ-constr :  ∀ s1 s2 → s1 <ₛ s2 → fst s1 <o fst s2

--   <↑s lt = ≤o-sucMono lt

--   smax-≤L = omax-≤L
--   smax-≤R {s1 = s1} = omax-≤R {o1 = fst s1}

--   smax-LUB {s1 = s1} {s2 = s2} {s = s} lt1 lt2 = omax-lub (snd s1) (snd s2) (snd s) lt1 lt2
--   smax-assocL {s1} {s2} {s3} = omax-assocL (fst s1) (fst s2) (fst s3)
--   smax-assocR {s1} {s2} {s3} = omax-assocR (fst s1) (fst s2) (fst s3)
--   smax-commut {s1} {s2} = omax-commut (fst s1) (fst s2)
--   smax-mono lt1 lt2 = omax-mono lt1 lt2
--   smax-monoL lt = omax-monoL lt
--   smax-monoR {s1 = s1} lt = omax-monoR {o1 = fst s1} lt
--   smax-strictMono lt1 lt2 = omax-strictMono lt1 lt2
--   ≤ₛ↑ {s = s} = ≤↑ (fst s)


--   accHelper : (s : Size) → Acc _<o_ (erase s) → Acc _<ₛ_ s
--   accHelper s (acc pf) = acc (λ x lt → accHelper x (pf (erase x) lt))

--   sizeWF s = accHelper s (ordWF (erase s))
--   sizeRec P f = WFI.induction sizeWF f


-- S1 : Size
-- S1 = S↑ SZ
