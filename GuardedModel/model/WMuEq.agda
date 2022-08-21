

{-# OPTIONS --cubical --guarded #-}



-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary

open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq hiding (_∎)
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
open import Cubical.Data.Equality using (ptoc ; ctop)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Sum
open import GuardedModality using (later-ext)

open import ApproxExact


--TODO: don't make ℓ module param
module WMuEq {{_ : DataTypes}} {{_ : DataGerms}} {{æ : Æ}} where

open import Code
-- open import Head
open import Util



-- More direct interpretation of inductive descriptions
-- Works because we ensure the paramter types are always codes, not types
-- So we can stay in Set
-- Also, Cubical Agda recognizes these as strictly decreasing, which is nice
data ℂDescEl' {ℓ} (cI : ℂ ℓ) (X : ApproxEl cI → Set) : {sig : IndSig} (cB : ℂ ℓ) →  ℂDesc cI cB sig → ApproxEl cI → ApproxEl cB → Set where
  ElEnd : ∀ {cB b i} j → i ≅ j →  ℂDescEl' cI X cB (CEnd j) i b
  ElArg : ∀ {cB cA sig i b} {D : ℂDesc cI _ sig} → (a : Approxed (El (cA b)) ) →  ℂDescEl' cI X (CΣ cB cA)  D i (b , approx a) → ℂDescEl' cI X cB (CArg cA D _ reflp) i b
  ElRec : ∀ {cB b i sig} {j : ApproxEl cI} {D : ℂDesc cI cB sig} →
    X j → ℂDescEl' cI X cB D i b → ℂDescEl' cI X cB  (CRec j D) i b
  ElHRec : ∀ {cB b i sig} {c : ApproxEl cB → ℂ ℓ} {j : (b : ApproxEl cB) → ApproxEl (c b) → ApproxEl cI} {D : ℂDesc cI cB sig} →
    ((x : Approxed (λ {{æ}} → El {{æ = æ}} (c b))) → X (j b (approx x))) → ℂDescEl' cI X cB D i b → ℂDescEl' cI X cB  (CHRec c j D) i b



ℂDescEl : ∀  {ℓ sig} {cI cB : ℂ ℓ} → ℂDesc cI cB sig → (ApproxEl cI → Set) → ApproxEl cI → ApproxEl cB → Set
ℂDescEl {cI = cI} {cB} D X i b = ℂDescEl' cI X cB D i b

-- Fixed Points of inductive descriptions from codes
-- We always ensure the first layer of descriptions is data-constructors
-- Since we use these for comparing things for consistency

data ℂμ {ℓ} {cI : ℂ ℓ} (tyCtor : CName) (D : DCtors tyCtor cI) (i : ApproxEl cI)  : Set where
  Cinit : (d : DName tyCtor) → ℂDescEl (D d) (ℂμ tyCtor D) i true → ℂμ  tyCtor D i
  Cμ⁇ Cμ℧ :  ℂμ tyCtor D  i


-- ℂμ1 : ∀ {ℓ} {cI : ℂ ℓ} (tyCtor : CName) (D : DName tyCtor → ℂDesc cI) (i : ApproxEl cI)  → Set
-- ℂμ1 tyCtor D i = Σ[ d ∈ DName tyCtor ] ℂDescEl (D d) (ℂμ tyCtor D) i

WArg : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : DCtors tyCtor cI) → ApproxEl cI →  Set
WArg D  = W (Arg λ d → interpDesc (D d) true) Unit


-- ℂElFContainer : ∀ {ℓ} {cI : ℂ ℓ} {i : ApproxEl cI} {X : ApproxEl cI → Set} → {D : ℂDesc cI} → ℂDescEl D X i ≡ FContainer (interpDesc D) X Unit i
-- ℂElFContainerExt : ∀ {ℓ} {cI : ℂ ℓ} {i : ApproxEl cI} {X : ApproxEl cI → Set} → {D : ℂDesc cI} → ℂDescEl D ≡ λ X i → FContainer (interpDesc D) X Unit i

-- Univalence gives us that this version of codes
-- is identical to the version given by W-types
-- I don't know if we'll actually use this, but it was an important sanity check
-- Proof is at the bottom of this file
ℂμWext : ∀ {ℓ} {cI : ℂ ℓ}  {tyCtor : CName} {D : DCtors tyCtor cI }  →
  ℂμ tyCtor D ≡ WArg D


ℂμW : ∀ {ℓ} {cI  : ℂ ℓ}  {tyCtor : CName} {D : DCtors tyCtor cI} {i : ApproxEl cI}  →
  ℂμ tyCtor D i ≡ WArg D i




------------------------------------------
-- Machinery for the isomorphism between W types and descriptions


fromCElCommand : ∀ {ℓ sig} {cI cB : ℂ ℓ} (D : ℂDesc cI cB sig) {i : ApproxEl cI} {X : ApproxEl cI → Set} {b : ApproxEl cB}
  → ℂDescEl  D X i b
  → CommandD D i b
fromCElCommand .(CEnd j) (ElEnd j x) = x
fromCElCommand (CArg _ D _ _) (ElArg a x) = a , fromCElCommand D x
fromCElCommand (CRec _ D) (ElRec x x₁) = fromCElCommand D x₁
fromCElCommand (CHRec c j D) (ElHRec f x) = fromCElCommand D x



fromCElF : ∀ {ℓ sig} {cI cB : ℂ ℓ} (D : ℂDesc cI cB sig) {X : ApproxEl cI → Set} {i : ApproxEl cI} {b : ApproxEl cB}
  → (x : ℂDescEl  D X i b)
  → (r : ResponseD D b (fromCElCommand D x ) )
      → X (inextD D b (fromCElCommand D x ) r)
fromCElF (CArg c D _ _) (ElArg a x) r = fromCElF D x r
fromCElF (CRec j D) (ElRec x x₁) (Rec _) = x
fromCElF (CRec i D) (ElRec x x₁) (Rest x₂) = fromCElF D x₁ x₂
fromCElF (CHRec c i D) (ElHRec f1 f2) (Rec a) = f1 a
fromCElF (CHRec c i D) (ElHRec f1 f2) (Rest r) = fromCElF D f2 r --fromCElF (D (approx a)) (f2 a) r



fromCμ : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} {D : DCtors tyCtor cI} {i : ApproxEl cI}
  → ℂμ tyCtor D i
  → WArg D i
fromCEl : ∀ {ℓ sig} {cI cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI cB sig) (E : DCtors tyCtor cI) {i : ApproxEl cI} {b : ApproxEl cB}
  → (x : ℂDescEl  D (ℂμ tyCtor E) i b)
  → (r : ResponseD D b (fromCElCommand D x))
      → WArg E (inextD D b (fromCElCommand D x ) r )


fromCμ {D = D} (Cinit d x) = Wsup (FC (d , fromCElCommand (D d) x) (fromCEl (D d) D x) (λ ()))
fromCμ Cμ⁇ = W⁇
fromCμ Cμ℧ = W℧

fromCEl (CArg c D _ _) E (ElArg a x) r = fromCEl D E x r
fromCEl (CRec i D) E (ElRec x x₁) (Rec _) = fromCμ x
fromCEl (CRec i D) E (ElRec x x₁) (Rest x₂) = fromCEl D E x₁ x₂
fromCEl (CHRec c i D) E (ElHRec f1 f2) (Rec a) = fromCμ (f1 a)
fromCEl (CHRec c i D) E (ElHRec f1 f2) (Rest r) = fromCEl D E f2 r



toCEl :
  ∀ {ℓ sig} {cI cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI cB sig) (E : DCtors tyCtor cI ) {ix : ApproxEl cI} {b : ApproxEl cB} →
  (com : CommandD D ix b) →
  (k : (r : ResponseD D b com ) →
                  WArg E (inextD D b com r))
  → □ {X = WArg E} (interpDesc D b)
      (λ (i , x) → ℂμ tyCtor E i)
      (ix , FC com k (λ _ → tt))
  -- FContainer (interpDesc D) (λ i → W (interpDesc E) Unit i × ℂμ E i) Unit ix
  → (ℂDescEl  D (ℂμ tyCtor E) ix b)


toCμ : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : DCtors tyCtor cI) {ix : ApproxEl cI}
  → (x : WArg D ix)
  → ℂμ tyCtor D ix
toCμ D = wInd (λ (i , _) → ℂμ _ D i) (λ {i} (FC (d , com) k _) φ → Cinit d (toCEl (D d) D com k φ)) Cμ℧ Cμ⁇


toCEl (CEnd i) E wit k φ = ElEnd i wit
toCEl (CArg c D _ reflp) E (a , com) k φ = ElArg a (toCEl D E com k φ)
toCEl (CRec j D) E com k φ = ElRec (φ (Rec tt)) (toCEl D E com (λ r → k (Rest r)) λ r → φ (Rest r))
toCEl (CHRec c j D) E com k φ = ElHRec (λ a → φ (Rec a)) (toCEl D E com (λ r → k (Rest r)) λ r → φ (Rest r))


toCElF :
  ∀ {ℓ sig} {cI cB : ℂ ℓ} {X : ApproxEl cI → Set} (D : ℂDesc cI cB sig)  {ix : ApproxEl cI} {b : ApproxEl cB} →
  (com : CommandD D ix b) →
  (k : (r : ResponseD D b com ) → X (inextD D b com r))
  → (ℂDescEl D X ix b)
toCElF (CEnd i) wit k = ElEnd i wit
toCElF (CArg c D _ reflp) (a , com) k = ElArg a (toCElF D com k)
toCElF (CRec j D) com k = ElRec (k (Rec tt)) (toCElF D com (λ r → k (Rest r)))
toCElF (CHRec c j D) com k = ElHRec (λ a → k (Rec a)) (toCElF D com (λ r → k (Rest r)))
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
fromToCElCommand (CHRec c j D) E com k   = fromToCElCommand D E com (λ r → k (Rest r))


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

fromToCEl :
  ∀ {ℓ sig} {cI cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI cB sig) (E : DCtors tyCtor cI) {ix : ApproxEl cI} {b : ApproxEl cB}
  → (com : CommandD D ix b)
  → (k : (r : ResponseD D b com ) →
                  WArg E (inextD D b com r))
  → (φ₂ : □ {X = WArg E} (interpDesc D b)
      (λ (i , x) →
         fromCμ (toCμ E x) ≡ x)
      (ix , FC com k (λ _ → tt)))
  → PathP (λ 𝕚 → let com = fromToCElCommand D E com k  𝕚 in (r : ResponseD D b com) → WArg E (inextD D b com r))
  (fromCEl D E (toCEl D E com k λ r → toCμ E (k r))) k
fromToCEl (CodeModule.CEnd i) E com k  φ = funExt (λ ())
fromToCEl (CodeModule.CArg c D _ reflp) E (a , com) k  φ  = fromToCEl D E com k φ
fromToCEl (CodeModule.CRec j D) E com k  φ 𝕚 (Rec tt) = φ (Rec tt) 𝕚
fromToCEl (CodeModule.CRec j D) E com k  φ 𝕚 (Rest r) = fromToCEl D E com (λ r → k (Rest r)) (λ r → φ (Rest r)) 𝕚 r
fromToCEl (CodeModule.CHRec c j D) E com k φ 𝕚 (Rec a) = φ (Rec a) 𝕚
fromToCEl (CodeModule.CHRec c j D) E com k φ 𝕚 (Rest r) = fromToCEl D E com (λ r → k (Rest r)) (λ r → φ (Rest r)) 𝕚 r


fromToCμ :  ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : DCtors tyCtor cI) {ix : ApproxEl cI}
  → (x : WArg D ix)
  → fromCμ (toCμ D x) ≡ x
fromToCμ {cI = cI} D = wInd
  (λ(ix , x) → fromCμ (toCμ D x) ≡ x) helper refl refl
  where
    helper : ∀ {i : ApproxEl cI} (cs : FContainer (Arg (λ d → interpDesc (D d) true)) (WArg D) Unit i)  →  (φ : _) → fromCμ (toCμ D (Wsup cs)) ≡ Wsup cs
    helper {i} (FC (d , com) k _) φ 𝕚 =
      Wsup (FC
        (d , fromToCElCommand (D d) D com k 𝕚)
        (fromToCEl (D d) D com k φ 𝕚)
        λ _ → tt)


toFromCμ : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} {D : DCtors tyCtor cI} {i : ApproxEl cI}
  → (x : ℂμ tyCtor D i)
  → toCμ D (fromCμ x) ≡ x
toFromCEl : ∀ {ℓ sig} {cI cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI cB sig) (E : DCtors tyCtor cI) {i : ApproxEl cI} {b : ApproxEl cB}
  → (x : ℂDescEl  D (ℂμ tyCtor E) i b)
  → toCEl D E (fromCElCommand D x) (fromCEl D E x) (λ r → toCμ E (fromCEl D E x r)) ≡ x

toFromCμ (Cinit d x) = cong (Cinit d) (toFromCEl _ _ x)
toFromCμ Cμ⁇ = refl
toFromCμ Cμ℧ = refl

toFromCEl .(CEnd j) E (ElEnd j x) = refl
toFromCEl (CArg c D _ reflp) E (ElArg a x) = cong (ElArg a) (toFromCEl D E x)
toFromCEl (CRec j D) E (ElRec x x₁) = cong₂ ElRec (toFromCμ x) (toFromCEl D E x₁)
toFromCEl (CHRec c j D) E (ElHRec x x₁) = cong₂ ElHRec (funExt (λ a → toFromCμ (x a))) (toFromCEl D E x₁)
-- toFromCEl (CHGuard c D1 D2) E (ElHGuard x x₁) = cong₂ ElHGuard (funExt λ a → toFromCEl D1 E (x a)) (toFromCEl D2 E x₁)



-- fromToCElF :
--   ∀ {ℓ} {cI : ℂ ℓ} (D : ℂDesc cI) {X : ApproxEl cI → Set} {ix : ApproxEl cI}
--   → (com : CommandD D ix)
--   → (k : (r : ResponseD D com ) →
--                   X (inextD D com r))
--   → PathP (λ 𝕚 → let com = fromToCElCommandF D com k  𝕚 in (r : ResponseD D com) → X (inextD D com r))
--     (fromCElF D {X = X} (toCElF {X = X} D com k)) k
-- fromToCElF (CodeModule.CEnd i) com k  = funExt (λ ())
-- fromToCElF (CodeModule.CArg c D) (a , com) k   = fromToCElF (D (approx a)) com k
-- fromToCElF (CodeModule.CRec j D) com k  𝕚 (Rec tt) = k (Rec tt)
-- fromToCElF (CodeModule.CRec j D) com k  𝕚 (Rest r) = fromToCElF D com (λ r → k (Rest r))  𝕚 r
-- fromToCElF (CodeModule.CHRec c j D) com k 𝕚 (Rec a) = k (Rec a)
-- fromToCElF (CodeModule.CHRec c j D) com k 𝕚 (Rest (a , r)) = fromToCElF (D (approx a)) (com a) (λ r → k (Rest (a , r)))  𝕚 r
-- -- fromToCElF (CodeModule.CHGuard c D D₁) (com1 , com2) k 𝕚 (GuardedArg (a , r)) = fromToCElF D (com1 a) (λ r → k (GuardedArg (a , r)))  𝕚 r
-- -- fromToCElF (CodeModule.CHGuard c D D₁) (com1 , com2) k 𝕚 (GRest r) = fromToCElF D₁ com2 (λ r → k (GRest r))  𝕚 r


-- toFromCElF : ∀ {ℓ} {cI : ℂ ℓ} (D : ℂDesc cI) {X : ApproxEl cI → Set} {i : ApproxEl cI}
--   → (x : ℂDescEl  D X i)
--   → toCElF D (fromCElCommand D x) (fromCElF D x) ≡ x
-- toFromCElF .(CEnd j) (ElEnd j x) = refl
-- toFromCElF (CArg c D) (ElArg a x) = cong (ElArg a) (toFromCElF (D (approx a)) x)
-- toFromCElF (CRec j D) (ElRec x x₁) = cong (ElRec x) (toFromCElF D x₁)
-- toFromCElF (CHRec c j D) (ElHRec x x₁) = cong (ElHRec x) (funExt λ a → toFromCElF (D (approx a)) (x₁ a))
-- -- toFromCElF (CHGuard c D1 D2) (ElHGuard x x₁) = cong₂ ElHGuard (funExt λ a → toFromCElF D1 (x a)) (toFromCElF D2 x₁)

CμWiso :
  ∀ {ℓ} {cI  : ℂ ℓ}  {tyCtor : CName} {D : DCtors tyCtor cI} {i : ApproxEl cI}
  → Iso (ℂμ tyCtor D i) (WArg D i)
CμWiso = (iso fromCμ (toCμ _) (fromToCμ _) toFromCμ)

ℂμW = isoToPath CμWiso

ℂμWext = funExt λ i → ℂμW {i = i}

-- -- ℂElFContainer {D = D} = isoToPath (iso
-- --   (λ x → FC (fromCElCommand D x) (fromCElF D x) (λ _ → tt))
-- --   (λ (FC com k _) → toCElF D com k)
-- --   (λ (FC com k unk) 𝕚 → FC (fromToCElCommandF D com k 𝕚) (fromToCElF D com k 𝕚) unk)
-- --   (toFromCElF D))

-- -- ℂElFContainerExt = funExt λ X → funExt (λ i → ℂElFContainer)


-- -- ℂμWProp : ∀ {ℓ} {cI : ℂ ℓ}  {tyCtor : CName} {D : DName tyCtor → ℂDesc cI}  →
-- --    W (Arg (λ a → interpDesc (D (approx a)))) Unit ≡p ℂμ tyCtor D
-- -- ℂμWProp = ctop (sym ℂμWext)


-- -- open import Agda.Builtin.Equality
-- -- open import Agda.Builtin.Equality.Rewrite
-- -- {-# REWRITE ℂμWProp #-}
