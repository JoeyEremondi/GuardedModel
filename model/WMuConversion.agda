

{-# OPTIONS --cubical --guarded  #-}



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
data ℂDescEl' {ℓ} (X : Set) : {sig : IndSig} (cB : ℂ ℓ) →  ℂDesc cB sig → ApproxEl cB → Set where
  ElEnd : ∀ {cB b} → ℂDescEl' X cB (CEnd) b
  ElArg : ∀ {cB cA sig b} {D : ℂDesc _ sig} → (a : El (cA b) ) →  ℂDescEl' X (CΣ cB cA)  D (b , approx a) → ℂDescEl' X cB (CArg cA D _ reflp) b
  ElRec : ∀ {cB b sig}  {D : ℂDesc cB sig} →
        X → ℂDescEl' X cB D b → ℂDescEl' X cB  (CRec D) b
  ElHRec : ∀ {cB b sig} {c : ApproxEl cB → ℂ ℓ} {D : ℂDesc cB sig} →
    ((x : El (c b)) → X ) → ℂDescEl' X cB D b → ℂDescEl' X cB  (CHRec c D _ reflp) b



ℂDescEl : ∀  {ℓ sig} {cB : ℂ ℓ} → ℂDesc cB sig → (X : Set) →  ApproxEl cB → Set
ℂDescEl {cB = cB} D X b = ℂDescEl' X cB D b

  -- Fixed Points of inductive descriptions from codes
  -- We always ensure the first layer of descriptions is data-constructors
  -- Since we use these for comparing things for consistency

data ℂμ {ℓ} (tyCtor : CName) (D : DCtors tyCtor)  : Set where
    Cinit : (d : DName tyCtor) → ℂDescEl {ℓ = ℓ} (D d) (ℂμ tyCtor D) Gtt → ℂμ  tyCtor D
    Cμ⁇ Cμ℧ :  ℂμ tyCtor D


  -- ℂμ1 : ∀ {ℓ} {cI : ℂ ℓ} (tyCtor : CName) (D : DName tyCtor → ℂDesc cI) (i : ApproxEl cI)  → Set
  -- ℂμ1 tyCtor D = Σ[ d ∈ DName tyCtor ] ℂDescEl (D d) (ℂμ tyCtor D) i

WArg : ∀ {ℓ} {tyCtor : CName} (D : DCtors {ℓ = ℓ} tyCtor) →   Set
WArg D  = W̃ (Arg λ d → interpDesc (D d) Gtt) tt


  -- ℂElFContainer : ∀ {ℓ} {cI : ℂ ℓ} {i : ApproxEl cI} {X :  Set} → {D : ℂDesc cI} → ℂDescEl D X ≡ FContainer (interpDesc D) X Unit i
  -- ℂElFContainerExt : ∀ {ℓ} {cI : ℂ ℓ} {i : ApproxEl cI} {X :  Set} → {D : ℂDesc cI} → ℂDescEl D ≡ λ X → FContainer (interpDesc D) X Unit i

  -- Univalence gives us that this version of codes
  -- is identical to the version given by W-types
  -- don't know if we'll actually use this, but it was an important sanity check
  -- Proof is at the bottom of this file
  -- ℂμWext : ∀ {ℓ} {cI : ℂ ℓ}  {tyCtor : CName} {D : DCtors tyCtor }  →
  --   ℂμ tyCtor D ≡ WArg D


  -- ℂμW : ∀ {ℓ} {cI  : ℂ ℓ}  {tyCtor : CName} {D : DCtors tyCtor cI} {i : ApproxEl cI}  →
  --   ℂμ tyCtor D ≡ WArg D i




  ------------------------------------------
  -- Machinery for the isomorphism between W types and descriptions


fromCElCommand : ∀ {ℓ sig} {cB : ℂ ℓ} (D : ℂDesc cB sig) {X :  Set} {b : ApproxEl cB}
    → ℂDescEl  D X b
    → CommandD D b
fromCElCommand .(CEnd) (ElEnd) = tt
fromCElCommand (CArg _ D _ _) (ElArg a x) = a , fromCElCommand D x
fromCElCommand (CRec D) (ElRec x x₁) = fromCElCommand D x₁
fromCElCommand (CHRec c D _ _) (ElHRec f x) = fromCElCommand D x



fromCElF : ∀ {ℓ sig} {cB : ℂ ℓ} (D : ℂDesc cB sig) {X :  Set} {b : ApproxEl cB}
    → (x : ℂDescEl  D X b)
    → (r : ResponseD D b (fromCElCommand D x) )
        → X
fromCElF (CArg c D _ _) (ElArg a x) r =  fromCElF D x r
fromCElF (CRec D) (ElRec x x₁) (Rec _) =  x
fromCElF (CRec D) (ElRec x x₁) (Rest x₂) = fromCElF D x₁ x₂
fromCElF (CHRec c D _ _) (ElHRec f1 f2) (Rec a) =  f1 a
fromCElF (CHRec c D _ _) (ElHRec f1 f2) (Rest r) =  fromCElF D f2 r --fromCElF (D (approx a)) (f2 a) r



fromCμ : ∀ {ℓ} {tyCtor : CName} {D : DCtors {ℓ = ℓ} tyCtor}
    → ℂμ tyCtor D
    → WArg D
fromCEl : ∀ {ℓ sig} {cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cB sig) (E : DCtors {ℓ = ℓ} tyCtor) {b : ApproxEl cB}
    → (x : ℂDescEl  D (ℂμ tyCtor E) b)
    → (r : ResponseD D b (fromCElCommand D x))
        → WArg E


fromCμ {D = D} (Cinit d x) = Wsup (FC (d , fromCElCommand (D d) x) (fromCEl (D d) D x))
fromCμ Cμ⁇ = W⁇
fromCμ Cμ℧ = W℧

fromCEl (CArg c D _ _) E (ElArg a x) r = fromCEl D E x r
fromCEl (CRec D) E (ElRec x x₁) (Rec _) = fromCμ x
fromCEl (CRec D) E (ElRec x x₁) (Rest x₂) = fromCEl D E x₁ x₂
fromCEl (CHRec c D _ _) E (ElHRec f1 f2) (Rec a) = fromCμ (f1 a)
fromCEl (CHRec c D _ _) E (ElHRec f1 f2) (Rest r) = fromCEl D E f2 r



toCEl :
  ∀ {ℓ sig} {cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cB sig) (E : DCtors {ℓ = ℓ} tyCtor ) {b : ApproxEl cB} →
  (com : CommandD D b) →
  (k : (r : ResponseD D b com ) →
                WArg E)
  → □ {X = λ _ → WArg E} (interpDesc D b)
    (λ (i , x) → ℂμ tyCtor E)
    (tt , FC com k)
-- FContainer (interpDesc D) (λ → W (interpDesc E) Unit × ℂμ E i) Unit ix
  → (ℂDescEl  D (ℂμ tyCtor E) b)


toCμ : ∀ {ℓ} {tyCtor : CName} (D : DCtors {ℓ = ℓ} tyCtor)
  → (x : WArg D)
  → ℂμ tyCtor D
toCμ D = wInd (λ (i , _) → ℂμ _ D) (λ {i} (FC (d , com) k) φ → Cinit d (toCEl (D d) D com k φ)) Cμ℧ Cμ⁇


toCEl (CEnd) E _ k φ = ElEnd
toCEl (CArg c D _ reflp) E (a , com) k φ = ElArg a (toCEl D E com k φ)
toCEl (CRec D) E com k φ = ElRec (φ (Rec tt)) (toCEl D E com (λ r → k (Rest r)) λ r → φ (Rest r))
toCEl (CHRec c D _ reflp) E com k φ = ElHRec (λ a → φ (Rec a)) (toCEl D E com (λ r → k (Rest r)) λ r → φ (Rest r))


toCElF :
  ∀ {ℓ sig} {cB : ℂ ℓ} {X :  Set} (D : ℂDesc cB sig)   {b : ApproxEl cB} →
  (com : CommandD D b) →
  (k : (r : ResponseD D b com ) → X)
  → (ℂDescEl D X b)
toCElF (CEnd) wit k = ElEnd
toCElF (CArg c D _ reflp) (a , com) k = ElArg a (toCElF D com k)
toCElF (CRec D) com k = ElRec (k (Rec tt)) (toCElF D com (λ r → k (Rest r)))
toCElF (CHRec c D _ reflp) com k = ElHRec (λ a → k (Rec a)) (toCElF D com (λ r → k (Rest r)))
-- toCElF (CHGuard c D D₁) (com1 , com2) k = ElHGuard (λ a → toCElF D (com1 a) (λ r → k (GuardedArg (a , r))) ) (toCElF D₁ com2 (λ r → k (GRest r)) )


fromToCElCommand :
  ∀ {ℓ sig} {cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cB sig) (E : DCtors tyCtor) {b : ApproxEl cB}
  → (com : CommandD D b)
  → (k : (r : ResponseD D b com ) →
                WArg E)
  → fromCElCommand D (toCEl D E com k λ r → toCμ E (k r)) ≡ com
fromToCElCommand (CEnd) E com k   = refl
fromToCElCommand (CArg c D _ reflp) E (a , com) k   = ΣPathP (refl , fromToCElCommand D E com k  )
fromToCElCommand (CRec D) E com k   = fromToCElCommand D E com (λ r → k (Rest r))
fromToCElCommand (CHRec c D _ reflp) E com k   = fromToCElCommand D E com (λ r → k (Rest r))


-- fromToCElCommandF :
--   ∀ {ℓ}  (D : ℂDesc cI) {X :  Set}  {ix : ApproxEl cI}
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
