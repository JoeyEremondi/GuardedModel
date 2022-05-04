

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
module InductiveCodes {{æ : Æ}} {{_ : Datatypes}} where

open import Code
-- open import Head
open import Util


-- More direct interpretation of inductive descriptions
-- Works because we ensure the paramter types are always codes, not types
-- So we can stay in Set
-- Also, Cubical Agda recognizes these as strictly decreasing, which is nice
data ℂDescEl' {ℓ} (cI : ℂ ℓ) (X : El cI → Set) :  ℂDesc cI → El cI → Set where
  ElEnd : ∀ { i} j → i ≅ j →  ℂDescEl' cI X (CEnd j) i
  ElArg : ∀ {cA D i} → (a : El cA) →  ℂDescEl' cI X  (D (inl a)) i → ℂDescEl' cI X  (CArg cA D) i
  ElRec : ∀ {i} {j : El cI} {D : ℂDesc cI} →
    X j → ℂDescEl' cI X  D i → ℂDescEl' cI X  (CRec j D) i
  ElHRec : ∀ {i} {cA : ℂ ℓ} {j : El cA → El cI} {D : (El cA ⊎ ▹El cA) → ℂDesc cI}
    → ((a : El cA) → (X (j a)))
    → ((a : El cA) → (ℂDescEl' cI X  (D (inl a)) i))
    → ℂDescEl' cI X  (CHRec cA j D) i
  -- ElHGuard : ∀ {i} {cA : ℂ ℓ} {D E : ℂDesc cI}
  --   → ((a : ▹ (El cA)) → (ℂDescEl' cI X D i) )
  --   → ℂDescEl' cI X E i
  --   → ℂDescEl' cI X (CHGuard cA D E) i



ℂDescEl : ∀  {ℓ} {cI : ℂ ℓ} → ℂDesc cI → (El cI → Set) → El cI → Set
ℂDescEl {cI = cI} D X i = ℂDescEl' cI X D i

-- Fixed Points of inductive descriptions from codes
-- We always ensure the first layer of descriptions is data-constructors
-- Since we use these for comparing things for consistency

data ℂμ {ℓ} {cI : ℂ ℓ} (tyCtor : CName) (D : DName tyCtor → ℂDesc cI) (i : El cI)  : Set where
  Cinit : (d : DName tyCtor) → ℂDescEl (D d) (ℂμ tyCtor D) i → ℂμ  tyCtor D i
  Cμ⁇ Cμ℧ :  ℂμ tyCtor D  i


ℂμ1 : ∀ {ℓ} {cI : ℂ ℓ} (tyCtor : CName) (D : DName tyCtor → ℂDesc cI) (i : El cI)  → Set
ℂμ1 tyCtor D i = Σ[ d ∈ DName tyCtor ] ℂDescEl (D d) (ℂμ tyCtor D) i

WArg : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : DName tyCtor → ℂDesc cI) → El cI → Set
WArg D = W (Arg λ a → interpDesc (D a)) Unit

ℂElFContainer : ∀ {ℓ} {cI : ℂ ℓ} {i : El cI} {X : El cI → Set} → {D : ℂDesc cI} → ℂDescEl D X i ≡ FContainer (interpDesc D) X Unit i
ℂElFContainerExt : ∀ {ℓ} {cI : ℂ ℓ} {i : El cI} {X : El cI → Set} → {D : ℂDesc cI} → ℂDescEl D ≡ λ X i → FContainer (interpDesc D) X Unit i

-- Univalence gives us that this version of codes
-- is identical to the version given by W-types
-- I don't know if we'll actually use this, but it was an important sanity check
-- Proof is at the bottom of this file
ℂμWext : ∀ {ℓ} {cI : ℂ ℓ}  {tyCtor : CName} {D : DName tyCtor → ℂDesc cI}  →
  ℂμ tyCtor D ≡ WArg D


ℂμW : ∀ {ℓ} {cI : ℂ ℓ}  {tyCtor : CName} {D : DName tyCtor → ℂDesc cI} {i : El cI}  →
  ℂμ tyCtor D i ≡ WArg D i




------------------------------------------
-- Machinery for the isomorphism between W types and descriptions


fromCElCommand : ∀ {ℓ} {cI : ℂ ℓ} (D : ℂDesc cI) {i : El cI} {X : El cI → Set}
  → ℂDescEl  D X i
  → CommandD D i
fromCElCommand .(CEnd j) (ElEnd j x) = x
fromCElCommand (CArg _ D) (ElArg a x) = a , fromCElCommand (D (inl a)) x
fromCElCommand (CRec _ D) (ElRec x x₁) = fromCElCommand D x₁
fromCElCommand (CHRec c j D) (ElHRec x f) a = fromCElCommand (D (inl a)) (f a)
-- fromCElCommand (CHGuard c D1 D2) (ElHGuard f x) = (λ a → fromCElCommand D1 (f a)) , (fromCElCommand D2 x)



fromCElF : ∀ {ℓ} {cI : ℂ ℓ} (D : ℂDesc cI) {X : El cI → Set} {i : El cI}
  → (x : ℂDescEl  D X i)
  → (r : ResponseD D (fromCElCommand D x))
      → X (inextD D (fromCElCommand D x) r)
fromCElF (CArg c D) (ElArg a x) r = fromCElF (D (inl a)) x r
fromCElF (CRec j D) (ElRec x x₁) (Rec _) = x
fromCElF (CRec i D) (ElRec x x₁) (Rest x₂) = fromCElF D x₁ x₂
fromCElF (CHRec c i D) (ElHRec f1 f2) (Rec a) = f1 a
fromCElF (CHRec c i D) (ElHRec f1 f2) (Rest (a , r)) = fromCElF (D (inl a)) (f2 a) r
-- fromCElF (CHGuard c D D2) (ElHGuard x x₁) (GuardedArg (a , r)) = fromCElF D (x a) r
-- fromCElF (CHGuard c D D2) (ElHGuard x x₁) (GRest r) = fromCElF D2 x₁ r



fromCμ : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} {D : DName tyCtor → ℂDesc cI} {i : El cI}
  → ℂμ tyCtor D i
  → WArg D i
fromCEl : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI) (E : DName tyCtor → ℂDesc cI) {i : El cI}
  → (x : ℂDescEl  D (ℂμ tyCtor E) i)
  → (r : ResponseD D (fromCElCommand D x))
      → W (Arg λ d → interpDesc (E d)) Unit (inextD D (fromCElCommand D x) r )


fromCμ {D = D} (Cinit d x) = Wsup (FC (d , fromCElCommand (D d) x) (fromCEl (D d) D x) (λ ()))
fromCμ Cμ⁇ = W⁇
fromCμ Cμ℧ = W℧

fromCEl (CArg c D) E (ElArg a x) r = fromCEl (D (inl a)) E x r
fromCEl (CRec i D) E (ElRec x x₁) (Rec _) = fromCμ x
fromCEl (CRec i D) E (ElRec x x₁) (Rest x₂) = fromCEl D E x₁ x₂
fromCEl (CHRec c i D) E (ElHRec f1 f2) (Rec a) = fromCμ (f1 a)
fromCEl (CHRec c i D) E (ElHRec f1 f2) (Rest (a , r)) = fromCEl (D (inl a)) E (f2 a) r
-- fromCEl (CHGuard c D D2) E (ElHGuard x x₁) (GuardedArg (a , r)) = fromCEl D E (x a) r
-- fromCEl (CHGuard c D D2) E (ElHGuard x x₁) (GRest r) = fromCEl D2 E x₁ r



toCEl :
  ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI) (E : DName tyCtor → ℂDesc cI) {ix : El cI} →
  (com : CommandD D ix) →
  (k : (r : ResponseD D com ) →
                  WArg E (inextD D com r))
  → □ {X = WArg E} (interpDesc D )
      (λ (i , x) → ℂμ tyCtor E i)
      (ix , FC com k (λ _ → tt))
  -- FContainer (interpDesc D) (λ i → W (interpDesc E) Unit i × ℂμ E i) Unit ix
  → (ℂDescEl  D (ℂμ tyCtor E) ix)


toCμ : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : DName tyCtor → ℂDesc cI) {ix : El cI}
  → (x : WArg D ix)
  → ℂμ tyCtor D ix
toCμ D = wInd (λ (i , _) → ℂμ _ D i) (λ {i} (FC (d , com) k _) φ → Cinit d (toCEl (D d) D com k φ)) Cμ℧ Cμ⁇


toCEl (CEnd i) E wit k φ = ElEnd i wit
toCEl (CArg c D) E (a , com) k φ = ElArg a (toCEl (D (inl a)) E com k φ)
toCEl (CRec j D) E com k φ = ElRec (φ (Rec tt)) (toCEl D E com (λ r → k (Rest r)) λ r → φ (Rest r))
toCEl (CHRec c j D) E com k φ = ElHRec (λ a → φ (Rec a)) (λ a → toCEl (D (inl a)) E (com a) (λ r → k (Rest (a , r))) λ r → φ (Rest (a , r)))
-- toCEl (CHGuard c D D₁) E (com1 , com2) k φ = ElHGuard (λ a → toCEl D E (com1 a) (λ r → k (GuardedArg (a , r))) λ r → φ (GuardedArg (a , r))) (toCEl D₁ E com2 (λ r → k (GRest r)) λ r → φ (GRest r))


toCElF :
  ∀ {ℓ} {cI : ℂ ℓ} {X : El cI → Set} (D : ℂDesc cI)  {ix : El cI} →
  (com : CommandD D ix) →
  (k : (r : ResponseD D com ) → X (inextD D com r))
  → (ℂDescEl  D X ix)
toCElF (CEnd i) wit k = ElEnd i wit
toCElF (CArg c D) (a , com) k = ElArg a (toCElF (D (inl a)) com k)
toCElF (CRec j D) com k = ElRec (k (Rec tt)) (toCElF D com (λ r → k (Rest r)))
toCElF (CHRec c j D) com k = ElHRec (λ a → k (Rec a)) (λ a → toCElF (D (inl a)) (com a) (λ r → k (Rest (a , r))))
-- toCElF (CHGuard c D D₁) (com1 , com2) k = ElHGuard (λ a → toCElF D (com1 a) (λ r → k (GuardedArg (a , r))) ) (toCElF D₁ com2 (λ r → k (GRest r)) )


fromToCElCommand :
  ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI) (E : DName tyCtor → ℂDesc cI ) {ix : El cI}
  → (com : CommandD D ix)
  → (k : (r : ResponseD D com ) →
                  WArg E (inextD D com r))
  → fromCElCommand D (toCEl D E com k λ r → toCμ E (k r)) ≡ com
fromToCElCommand (CEnd i) E com k   = refl
fromToCElCommand (CArg c D) E (a , com) k   = ΣPathP (refl , fromToCElCommand (D (inl a)) E com k  )
fromToCElCommand (CRec j D) E com k   = fromToCElCommand D E com (λ r → k (Rest r))
fromToCElCommand (CHRec c j D) E com k   = funExt λ a → fromToCElCommand (D (inl a)) E (com a) (λ r → k (Rest (a , r)))
-- fromToCElCommand (CHGuard c D D₁) E (com1 , com2) k   =
  -- ≡-×
  --   (funExt (λ a → fromToCElCommand D E (com1 a) (λ r → k (GuardedArg (a , r)))  ))
  --   (fromToCElCommand D₁ E com2 (λ r → k (GRest r))  )


fromToCElCommandF :
  ∀ {ℓ} {cI : ℂ ℓ} (D : ℂDesc cI) {X : El cI → Set}  {ix : El cI}
  → (com : CommandD D ix)
  → (k : (r : ResponseD D com ) →
                  X (inextD D com r))
  → fromCElCommand D (toCElF {X = X} D com k) ≡ com
fromToCElCommandF (CEnd i) com k   = refl
fromToCElCommandF (CArg c D) (a , com) k   = ΣPathP (refl , fromToCElCommandF (D (inl a)) com k  )
fromToCElCommandF (CRec j D) com k   = fromToCElCommandF D com (λ r → k (Rest r))
fromToCElCommandF (CHRec c j D) com k   = funExt λ a → fromToCElCommandF (D (inl a)) (com a) (λ r → k (Rest (a , r)))
-- fromToCElCommandF (CHGuard c D D₁) (com1 , com2) k   =
  -- ≡-×
  --   (funExt (λ a → fromToCElCommandF D (com1 a) (λ r → k (GuardedArg (a , r)))  ))
  --   (fromToCElCommandF D₁ com2 (λ r → k (GRest r))  )

fromToCEl :
  ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI) (E : DName tyCtor → ℂDesc cI) {ix : El cI}
  → (com : CommandD D ix)
  → (k : (r : ResponseD D com ) →
                  WArg E (inextD D com r))
  → (φ₂ : □ {X = WArg E} (interpDesc D)
      (λ (i , x) →
         fromCμ (toCμ E x) ≡ x)
      (ix , FC com k (λ _ → tt)))
  → PathP (λ 𝕚 → let com = fromToCElCommand D E com k  𝕚 in (r : ResponseD D com) → WArg E (inextD D com r))
  (fromCEl D E (toCEl D E com k λ r → toCμ E (k r))) k
fromToCEl (CodeModule.CEnd i) E com k  φ = funExt (λ ())
fromToCEl (CodeModule.CArg c D) E (a , com) k  φ  = fromToCEl (D (inl a)) E com k φ
fromToCEl (CodeModule.CRec j D) E com k  φ 𝕚 (Rec tt) = φ (Rec tt) 𝕚
fromToCEl (CodeModule.CRec j D) E com k  φ 𝕚 (Rest r) = fromToCEl D E com (λ r → k (Rest r)) (λ r → φ (Rest r)) 𝕚 r
fromToCEl (CodeModule.CHRec c j D) E com k φ 𝕚 (Rec a) = φ (Rec a) 𝕚
fromToCEl (CodeModule.CHRec c j D) E com k φ 𝕚 (Rest (a , r)) = fromToCEl (D (inl a)) E (com a) (λ r → k (Rest (a , r))) (λ r → φ (Rest (a , r))) 𝕚 r
-- fromToCEl (CodeModule.CHGuard c D D₁) E (com1 , com2) k φ 𝕚 (GuardedArg (a , r)) = fromToCEl D E (com1 a) (λ r → k (GuardedArg (a , r))) (λ r → φ (GuardedArg (a , r))) 𝕚 r
-- fromToCEl (CodeModule.CHGuard c D D₁) E (com1 , com2) k φ 𝕚 (GRest r) = fromToCEl D₁ E com2 (λ r → k (GRest r)) (λ r → φ (GRest r)) 𝕚 r


fromToCμ :  ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : DName tyCtor → ℂDesc cI) {ix : El cI}
  → (x : WArg D ix)
  → fromCμ (toCμ D x) ≡ x
fromToCμ {cI = cI} D = wInd
  (λ(ix , x) → fromCμ (toCμ D x) ≡ x) helper refl refl
  where
    helper : ∀ {i : El cI} (cs : FContainer (Arg (λ d → interpDesc (D d))) (WArg D) Unit i)  →  (φ : _) → fromCμ (toCμ D (Wsup cs)) ≡ Wsup cs
    helper {i} (FC (d , com) k _) φ 𝕚 =
      Wsup (FC
        (d , fromToCElCommand (D d) D com k 𝕚)
        (fromToCEl (D d) D com k φ 𝕚)
        λ _ → tt)


toFromCμ : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} {D : DName tyCtor → ℂDesc cI} {i : El cI}
  → (x : ℂμ tyCtor D i)
  → toCμ D (fromCμ x) ≡ x
toFromCEl : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI) (E : DName tyCtor → ℂDesc cI) {i : El cI}
  → (x : ℂDescEl  D (ℂμ tyCtor E) i)
  → toCEl D E (fromCElCommand D x) (fromCEl D E x) (λ r → toCμ E (fromCEl D E x r)) ≡ x
  -- → toCEl D E (fromCElCommand D x) (λ r → fromCEl D E x r , toCμ E (fromCEl D E x r)) ≡ x

toFromCμ (Cinit d x) = cong (Cinit d) (toFromCEl _ _ x)
toFromCμ Cμ⁇ = refl
toFromCμ Cμ℧ = refl

toFromCEl .(CEnd j) E (ElEnd j x) = refl
toFromCEl (CArg c D) E (ElArg a x) = cong (ElArg a) (toFromCEl (D (inl a)) E x)
toFromCEl (CRec j D) E (ElRec x x₁) = cong₂ ElRec (toFromCμ x) (toFromCEl D E x₁)
toFromCEl (CHRec c j D) E (ElHRec x x₁) = cong₂ ElHRec (funExt (λ a → toFromCμ (x a))) (funExt λ a → toFromCEl (D (inl a)) E (x₁ a))
-- toFromCEl (CHGuard c D1 D2) E (ElHGuard x x₁) = cong₂ ElHGuard (funExt λ a → toFromCEl D1 E (x a)) (toFromCEl D2 E x₁)



fromToCElF :
  ∀ {ℓ} {cI : ℂ ℓ} (D : ℂDesc cI) {X : El cI → Set} {ix : El cI}
  → (com : CommandD D ix)
  → (k : (r : ResponseD D com ) →
                  X (inextD D com r))
  → PathP (λ 𝕚 → let com = fromToCElCommandF D com k  𝕚 in (r : ResponseD D com) → X (inextD D com r))
    (fromCElF D {X = X} (toCElF {X = X} D com k)) k
fromToCElF (CodeModule.CEnd i) com k  = funExt (λ ())
fromToCElF (CodeModule.CArg c D) (a , com) k   = fromToCElF (D (inl a)) com k
fromToCElF (CodeModule.CRec j D) com k  𝕚 (Rec tt) = k (Rec tt)
fromToCElF (CodeModule.CRec j D) com k  𝕚 (Rest r) = fromToCElF D com (λ r → k (Rest r))  𝕚 r
fromToCElF (CodeModule.CHRec c j D) com k 𝕚 (Rec a) = k (Rec a)
fromToCElF (CodeModule.CHRec c j D) com k 𝕚 (Rest (a , r)) = fromToCElF (D (inl a)) (com a) (λ r → k (Rest (a , r)))  𝕚 r
-- fromToCElF (CodeModule.CHGuard c D D₁) (com1 , com2) k 𝕚 (GuardedArg (a , r)) = fromToCElF D (com1 a) (λ r → k (GuardedArg (a , r)))  𝕚 r
-- fromToCElF (CodeModule.CHGuard c D D₁) (com1 , com2) k 𝕚 (GRest r) = fromToCElF D₁ com2 (λ r → k (GRest r))  𝕚 r


toFromCElF : ∀ {ℓ} {cI : ℂ ℓ} (D : ℂDesc cI) {X : El cI → Set} {i : El cI}
  → (x : ℂDescEl  D X i)
  → toCElF D (fromCElCommand D x) (fromCElF D x) ≡ x
toFromCElF .(CEnd j) (ElEnd j x) = refl
toFromCElF (CArg c D) (ElArg a x) = cong (ElArg a) (toFromCElF (D (inl a)) x)
toFromCElF (CRec j D) (ElRec x x₁) = cong (ElRec x) (toFromCElF D x₁)
toFromCElF (CHRec c j D) (ElHRec x x₁) = cong (ElHRec x) (funExt λ a → toFromCElF (D (inl a)) (x₁ a))
-- toFromCElF (CHGuard c D1 D2) (ElHGuard x x₁) = cong₂ ElHGuard (funExt λ a → toFromCElF D1 (x a)) (toFromCElF D2 x₁)


ℂμW = isoToPath (iso fromCμ (toCμ _) (fromToCμ _) toFromCμ)

ℂμWext = funExt λ i → ℂμW {i = i}

ℂElFContainer {D = D} = isoToPath (iso
  (λ x → FC (fromCElCommand D x) (fromCElF D x) (λ _ → tt))
  (λ (FC com k _) → toCElF D com k)
  (λ (FC com k unk) 𝕚 → FC (fromToCElCommandF D com k 𝕚) (fromToCElF D com k 𝕚) unk)
  (toFromCElF D))

ℂElFContainerExt = funExt λ X → funExt (λ i → ℂElFContainer)


-- ℂμWProp : ∀ {ℓ} {cI : ℂ ℓ}  {tyCtor : CName} {D : DName tyCtor → ℂDesc cI}  →
--    W (Arg (λ a → interpDesc (D (inl a)))) Unit ≡p ℂμ tyCtor D
-- ℂμWProp = ctop (sym ℂμWext)


-- open import Agda.Builtin.Equality
-- open import Agda.Builtin.Equality.Rewrite
-- {-# REWRITE ℂμWProp #-}
