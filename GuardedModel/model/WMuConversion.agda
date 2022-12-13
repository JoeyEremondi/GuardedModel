

{-# OPTIONS --cubical --guarded --rewriting #-}



-- open import Guarded
open import Cubical.Data.Maybe as Maybe
open import Level
open import Cubical.Relation.Nullary

open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (⊥ to 𝟘)
-- open import Cubical.Data.Prod
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Inductives
open import GuardedAlgebra
open import Cubical.Induction.WellFounded
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Sum as Sum
open import GuardedModality using (later-ext)

open import ApproxExact
open import Code


--TODO: don't make ℓ module param
module WMuConversion {{_ : DataTypes}} {{_ : DataGerms}}  where

-- We only ever attach a size to the approximate part of a computation
-- and we only need this conversion for making a size
private
  instance
    approxÆ : Æ
    approxÆ = Approx



-- More direct interpretation of inductive descriptions
-- Works because we ensure the paramter types are always codes, not types
-- So we can stay in Set
-- Also, Cubical Agda recognizes these as strictly decreasing, which is nice
data ℂDescEl' {ℓ} (cI : ℂ ℓ) (X : ApproxEl cI → Set) : {sig : IndSig} (cB : ℂ ℓ) →  ℂDesc cI cB sig → ApproxEl cI → ApproxEl cB → Set where
  ElEnd : ∀ {cB b i} j → i ≅ j →  ℂDescEl' cI X cB (CEnd j) i b
  ElArg : ∀ {cB cA sig i b} {D : ℂDesc cI _ sig} → (a : El (cA b) ) →  ℂDescEl' cI X (CΣ cB cA)  D i (b , approx a) → ℂDescEl' cI X cB (CArg cA D _ reflp) i b
  ElRec : ∀ {cB b i sig} {j : ApproxEl cI} {D : ℂDesc cI cB sig} →
        X j → ℂDescEl' cI X cB D i b → ℂDescEl' cI X cB  (CRec j D) i b
  ElHRec : ∀ {cB b i sig} {c : ApproxEl cB → ℂ ℓ} {j : (b : ApproxEl cB) → ApproxEl (c b) → ApproxEl cI} {D : ℂDesc cI cB sig} →
    ((x : El (c b)) → X (j b (approx x))) → ℂDescEl' cI X cB D i b → ℂDescEl' cI X cB  (CHRec c j D _ reflp) i b



ℂDescEl : ∀  {ℓ sig} {cI cB : ℂ ℓ} → ℂDesc cI cB sig → (X : ApproxEl cI → Set) → ApproxEl cI → ApproxEl cB → Set
ℂDescEl {cI = cI} {cB} D X i b = ℂDescEl' cI X cB D i b

  -- Fixed Points of inductive descriptions from codes
  -- We always ensure the first layer of descriptions is data-constructors
  -- Since we use these for comparing things for consistency

data ℂμ {ℓ} {cI : ℂ ℓ} (tyCtor : CName) (D : DCtors tyCtor cI) (i : ApproxEl cI)  : Set where
    Cinit : (d : DName tyCtor) → ℂDescEl (D d) (ℂμ tyCtor D) i tt → ℂμ  tyCtor D i
    Cμ⁇ Cμ℧ :  ℂμ tyCtor D  i


  -- ℂμ1 : ∀ {ℓ} {cI : ℂ ℓ} (tyCtor : CName) (D : DName tyCtor → ℂDesc cI) (i : ApproxEl cI)  → Set
  -- ℂμ1 tyCtor D i = Σ[ d ∈ DName tyCtor ] ℂDescEl (D d) (ℂμ tyCtor D) i

WArg : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : DCtors tyCtor cI) → ApproxEl cI →  Set
WArg D  = W̃ (Arg λ d → interpDesc (D d) tt)


  -- ℂElFContainer : ∀ {ℓ} {cI : ℂ ℓ} {i : ApproxEl cI} {X : ApproxEl cI → Set} → {D : ℂDesc cI} → ℂDescEl D X i ≡ FContainer (interpDesc D) X Unit i
  -- ℂElFContainerExt : ∀ {ℓ} {cI : ℂ ℓ} {i : ApproxEl cI} {X : ApproxEl cI → Set} → {D : ℂDesc cI} → ℂDescEl D ≡ λ X i → FContainer (interpDesc D) X Unit i

  -- Univalence gives us that this version of codes
  -- is identical to the version given by W-types
  -- I don't know if we'll actually use this, but it was an important sanity check
  -- Proof is at the bottom of this file
  -- ℂμWext : ∀ {ℓ} {cI : ℂ ℓ}  {tyCtor : CName} {D : DCtors tyCtor cI }  →
  --   ℂμ tyCtor D ≡ WArg D


  -- ℂμW : ∀ {ℓ} {cI  : ℂ ℓ}  {tyCtor : CName} {D : DCtors tyCtor cI} {i : ApproxEl cI}  →
  --   ℂμ tyCtor D i ≡ WArg D i




  ------------------------------------------
  -- Machinery for the isomorphism between W types and descriptions


fromCElCommand : ∀ {ℓ sig} {cI cB : ℂ ℓ} (D : ℂDesc cI cB sig) {i : ApproxEl cI} {X : ApproxEl cI → Set} {b : ApproxEl cB}
    → ℂDescEl  D X i b
    → CommandD D i b
fromCElCommand .(CEnd j) (ElEnd j x) = x
fromCElCommand (CArg _ D _ _) (ElArg a x) = a , fromCElCommand D x
fromCElCommand (CRec _ D) (ElRec x x₁) = fromCElCommand D x₁
fromCElCommand (CHRec c j D _ _) (ElHRec f x) = fromCElCommand D x



fromCElF : ∀ {ℓ sig} {cI cB : ℂ ℓ} (D : ℂDesc cI cB sig) {X : ApproxEl cI → Set} {i : ApproxEl cI} {b : ApproxEl cB}
    → (x : ℂDescEl  D X i b)
    → (r : ResponseD D b (fromCElCommand D x) )
        → X (inextD D b  _ r)
fromCElF (CArg c D _ _) (ElArg a x) r =  fromCElF D x r
fromCElF (CRec j D) (ElRec x x₁) (Rec _) =  x
fromCElF (CRec i D) (ElRec x x₁) (Rest x₂) = fromCElF D x₁ x₂
fromCElF (CHRec c i D _ _) (ElHRec f1 f2) (Rec a) =  f1 a
fromCElF (CHRec c i D _ _) (ElHRec f1 f2) (Rest r) =  fromCElF D f2 r --fromCElF (D (approx a)) (f2 a) r



fromCμ : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} {D : DCtors tyCtor cI} {i : ApproxEl cI}
    → ℂμ tyCtor D i
    → WArg D i
fromCEl : ∀ {ℓ sig} {cI cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI cB sig) (E : DCtors tyCtor cI) {i : ApproxEl cI} {b : ApproxEl cB}
    → (x : ℂDescEl  D (ℂμ tyCtor E) i b)
    → (r : ResponseD D b (fromCElCommand D x))
        → WArg E (inextD D b (fromCElCommand D x) r)


fromCμ {D = D} (Cinit d x) = Wsup (FC (d , fromCElCommand (D d) x) (fromCEl (D d) D x))
fromCμ Cμ⁇ = W⁇
fromCμ Cμ℧ = W℧

fromCEl (CArg c D _ _) E (ElArg a x) r = fromCEl D E x r
fromCEl (CRec i D) E (ElRec x x₁) (Rec _) = fromCμ x
fromCEl (CRec i D) E (ElRec x x₁) (Rest x₂) = fromCEl D E x₁ x₂
fromCEl (CHRec c i D _ _) E (ElHRec f1 f2) (Rec a) = fromCμ (f1 a)
fromCEl (CHRec c i D _ _) E (ElHRec f1 f2) (Rest r) = fromCEl D E f2 r



toCEl :
  ∀ {ℓ sig} {cI cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI cB sig) (E : DCtors tyCtor cI ) {ix : ApproxEl cI} {b : ApproxEl cB} →
  (com : CommandD D ix b) →
  (k : (r : ResponseD D b com ) →
                WArg E (inextD D b com r))
  → □ {X = WArg E} (interpDesc D b)
    (λ (i , x) → ℂμ tyCtor E i)
    (ix , FC com k)
-- FContainer (interpDesc D) (λ i → W (interpDesc E) Unit i × ℂμ E i) Unit ix
  → (ℂDescEl  D (ℂμ tyCtor E) ix b)


toCμ : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : DCtors tyCtor cI) {ix : ApproxEl cI}
  → (x : WArg D ix)
  → ℂμ tyCtor D ix
toCμ D = wInd (λ (i , _) → ℂμ _ D i) (λ {i} (FC (d , com) k) φ → Cinit d (toCEl (D d) D com k φ)) Cμ℧ Cμ⁇


toCEl (CEnd i) E wit k φ = ElEnd i wit
toCEl (CArg c D _ reflp) E (a , com) k φ = ElArg a (toCEl D E com k φ)
toCEl (CRec j D) E com k φ = ElRec (φ (Rec tt)) (toCEl D E com (λ r → k (Rest r)) λ r → φ (Rest r))
toCEl (CHRec c j D _ reflp) E com k φ = ElHRec (λ a → φ (Rec a)) (toCEl D E com (λ r → k (Rest r)) λ r → φ (Rest r))


toCElF :
  ∀ {ℓ sig} {cI cB : ℂ ℓ} {X : ApproxEl cI → Set} (D : ℂDesc cI cB sig)  {ix : ApproxEl cI} {b : ApproxEl cB} →
  (com : CommandD D ix b) →
  (k : (r : ResponseD D b com ) → X (inextD D b com r))
  → (ℂDescEl D X ix b)
toCElF (CEnd i) wit k = ElEnd i wit
toCElF (CArg c D _ reflp) (a , com) k = ElArg a (toCElF D com k)
toCElF (CRec j D) com k = ElRec (k (Rec tt)) (toCElF D com (λ r → k (Rest r)))
toCElF (CHRec c j D _ reflp) com k = ElHRec (λ a → k (Rec a)) (toCElF D com (λ r → k (Rest r)))
-- toCElF (CHGuard c D D₁) (com1 , com2) k = ElHGuard (λ a → toCElF D (com1 a) (λ r → k (GuardedArg (a , r))) ) (toCElF D₁ com2 (λ r → k (GRest r)) )


fromToCElCommand :
  ∀ {ℓ sig} {cI cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI cB sig) (E : DCtors tyCtor cI) {ix : ApproxEl cI} {b : ApproxEl cB}
  → (com : CommandD D ix b)
  → (k : (r : ResponseD D b com ) →
                WArg E (inextD D b com r))
  → fromCElCommand D (toCEl D E com k λ r → toCμ E (k r)) ≡ com
fromToCElCommand (CEnd i) E com k   = refl
fromToCElCommand (CArg c D _ reflp) E (a , com) k   = ΣPathP (refl , fromToCElCommand D E com k  )
fromToCElCommand (CRec j D) E com k   = fromToCElCommand D E com (λ r → k (Rest r))
fromToCElCommand (CHRec c j D _ reflp) E com k   = fromToCElCommand D E com (λ r → k (Rest r))


-- fromToCElCommandF :
--   ∀ {ℓ} {cI : ℂ ℓ} (D : ℂDesc cI) {X : ApproxEl cI → Set}  {ix : ApproxEl cI}
--   → (com : CommandD D ix)
--   → (k : (r : ResponseD D com ) →
--                   X (inextD D com r))
--   → fromCElCommand D (toCElF {X = X} D com k) ≡ com
-- fromToCElCommandF (CEnd i) com k   = refl
-- fromToCElCommandF (CArg c D) (a , com) k   = ΣPathP (refl , fromToCElCommandF (D (approx a)) com k  )
-- fromToCElCommandF (CRec j D) com k   = fromToCElCommandF D com (λ r → k (Rest r))
-- fromToCElCommandF (CHRec c j D) com k   = funExt λ a → fromToCElCommandF (D (approx a)) (com a) (λ r → k (Rest (a , r)))
-- -- fromToCElCommandF (CHGuard c D D₁) (com1 , com2) k   =
--   -- ≡-×
--   --   (funExt (λ a → fromToCElCommandF D (com1 a) (λ r → k (GuardedArg (a , r)))  ))
--   --   (fromToCElCommandF D₁ com2 (λ r → k (GRest r))  )
