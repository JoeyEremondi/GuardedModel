

-- Inductive Descriptions for Gradual Datatypes

open import Level
open import Cubical.Data.Nat renaming (Unit to 𝟙)
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.FinData
open import Cubical.Data.Bool renaming (Bool to 𝟚)

open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
open import DecPEq

-- open import Cubical.Data.Bool
open import GuardedAlgebra

open import ApproxExact
module Inductives {{_ : Æ}} where


ISet : Set → Set1
ISet X = X → Set

-- data DTag : Set where
--   DE DA DR DHR DP DHP DHG : DTag

-- data IsRec : Set where
--   YesRec NoRec : IsRec

-- _&R&_ : IsRec → IsRec → IsRec
-- YesRec &R& y = YesRec
-- NoRec &R& y = y



data _≅_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where
  _⊢_≅_ : A → (x y : A ) →   x ≅ y


--Shamelessley copied from
-- The Agda standard library

infix 5 _◃_◃_/_

record Container (I : Set)  : Set1 where
  constructor _◃_◃_/_
  field
    Command  : (i : I) → Set
    Response : ∀ {i} → Command i → Set
    -- ResponseÆ : ∀ {i} → Command i → Set
    ResponseUnk : ∀ {i} → Command i → Set
    inext     : ∀ {i} (c : Command i) → Response c → I

open Container public

Arg : ∀ {A I : Set} → (A → Container I) → Container I
Command (Arg {A} f) i = Σ[ a ∈ A ] Command (f a) i
Response (Arg f) (a , com) = Response (f a) com
-- ResponseÆ (Arg f) (a , com) = ResponseÆ (f a) com
ResponseUnk (Arg f) (a , com) = ResponseUnk (f a) com
inext (Arg f) (a , com) r = inext (f a) com r

-- The semantics ("extension") of an indexed container.

record FContainer {I} (C : Container I) (X : I → Set) (Unk : Set) (i : I) : Set where
  constructor FC
  field
    command : Command C i
    responseNow :
      (r : Response C command)
      → X (inext C command r)
    -- responseLater :
    --   (r : Response C command)
    --   → ∀ j
    --   → j ≅ inext C command r
    --   → LÆ (X j)
    responseUnk : ResponseUnk C command → Unk




-- TODO : can't implement the full traversals until we have meet for indices
□ : ∀ {I Unk} {X : I → Set} (C : Container I) →  ((Σ I X) → Set) → (Σ I (FContainer C X Unk)) → Set
□ C P (i , (FC c k u)) = ∀ r → P (inext C c r , k r)

--   -- Any.

-- ◇ : ∀ {I Unk} {X : I → Set} (C : Container I) → ((Σ I X) → Set) → (Σ I (FContainer C X Unk)) → Set
-- ◇ C P (i , (FC c res u)) = Σ[ r ∈ Response C c ] (P (inext C c r , res r))

-- --Shamelessley copied from
-- -- The Agda standard library
-- --
-- -- Indexed W-types aka Petersson-Synek trees
-- ------------------------------------------------------------------------

-- -- The family of indexed W-types.

data W {I : Set} (C : Container I) (Unk : Set) (i : I)  :  Set where
  Wsup : FContainer C  (W C Unk) Unk i → W C Unk i
  W℧ W⁇ : W C Unk i
  -- Projections.

W1 : ∀ {I : Set} (C : Container I) (Unk : Set) (i : I) → Set
W1 C Unk = FContainer C (W C Unk) Unk

-- head : ∀ {I Unk i} {C : Container I} →  W C Unk i → Command C i
-- head (sup (FC c now later unk)) = c

-- tail : ∀ {I Unk} {C : Container I} {i} (w : W C Unk i) (r : Response C (head w)) → W C Unk (inext C (head w) r)
-- tail {I = I} (sup (_ , _ , k)) r = k r {!!} {!!}

-- --   -- Induction, (primitive) recursion and iteration.

wInd : ∀ {I Unk} {C : Container I} (P : Σ I (W C Unk) → Set) →
        (∀ {i} (cs : FContainer C (W C Unk) Unk i) → □ C P (i , cs) → P (i , Wsup cs)) →
        (∀ {i} → P (i , W℧ {i = i})) →
        (∀ {i} → P (i , W⁇ {i = i})) →
        ∀ {i} (w : W C Unk i) → P (i , w)
wInd P φ base℧ base⁇ (Wsup (FC c k u)) = φ (FC c k u) (λ r → wInd P φ base℧ base⁇ (k r))
wInd P φ base℧ base⁇ W℧ = base℧
wInd P φ base℧ base⁇ W⁇ = base⁇

wRec : ∀ {I Unk} {C : Container I} {X : I → Set} → (∀ {i} → FContainer C (λ i → W C Unk i × X i) Unk i → X i) → (∀ i → X i × X i) → ∀ {i} → W C Unk i → X i
wRec φ base (Wsup (FC c k u))= φ (FC c (λ r → (k r , wRec φ base (k r))) u)
wRec φ base W℧ = fst (base _)
wRec φ base W⁇ = snd (base _)

-- wIter : ∀ {I} {C : Container I} {X : I → Set} → (∀ {i} → ⟦ C ⟧ X i →  X i) → ∀ {i} → W C i → X i
-- wIter φ (sup (c , k))= φ (c , λ r → wIter φ (k r))



-- -- Adapted From Larry Diehls' thesis
-- -- https://pdxscholar.library.pdx.edu/cgi/viewcontent.cgi?article=4656&context=open_access_etds
-- -- THese are descriptions of 2-argument functors, so we can separately describe
-- -- strictly positive uses of ⁇ and Self
-- data Desc2 (I : Set) : (hasRec : IsRec) → Set1 where
--     End : (i : I) → Desc2 I NoRec
--     Arg : {r : IsRec} (A : Set) (D : A → Desc2 I r) → Desc2 I r
--     Rec : (i :  I) (D : Desc2 I r) → Desc2 I YesRec
--     HRec : {r : IsRec} (A : Set) (i : A → I) (D : A → Desc2 I r) → Desc2 I YesRec
--     Par : (D : Desc2 I r) → Desc2 I r
--     HPar : (A : Set)  (D : A → Desc2 I r) → Desc2 I r
--     HGuard : ∀ {r1 r2 r3 : IsRec} → (A : Set) → (D : Desc2 I r1 ) → (E : Desc2 I r2) → r3 ≡p r1 &R& r2 → Desc2 I r3




-- FDesc2 : ∀ {I} {r} → (D : Desc2 I r) → Set → ISet I → ISet I
-- FDesc2 {I} (End j) Unk X i  = Wit I i j
-- FDesc2 (Arg A D) Unk X i =  (Σ[ a ∈ A ] (FDesc2 (D a) Unk X i  ))
-- FDesc2 (Rec j D) Unk X i =  (X j × FDesc2 D Unk X i)
-- FDesc2 (HRec A j D) Unk X i =  (a : A) → (LÆ (X (j a)) × FDesc2 (D a) Unk X i)
-- FDesc2 (Par D) Unk X i =  Unk × FDesc2 (D) Unk X i
-- FDesc2 (HPar A D) Unk X i =  ((a : A) → LÆ Unk × FDesc2 (D a) Unk X i)
-- FDesc2 (HGuard A D E pf) Unk X i =  ((a : ▹ A) → LÆ (FDesc2 D Unk X i)) × FDesc2 E Unk X i

-- FDesc : ∀ {I r} → (D : Desc2 I r) → ISet I  → ISet I
-- FDesc D X i = FDesc2 D 𝟙 X i

-- --Gradual Fixed-point of a description's functor
-- --Essentially adds two constructors for ? and ℧
-- data μ2 {I r} (D : Desc2 I r) (Unk : Set) (i : I)  : Set where
--   init : FDesc2 D Unk (μ2 D Unk) i → μ2 D Unk i
--   μ⁇ μ℧ :  μ2 D Unk i


-- μ : ∀ {I} (D : Desc2 I r)  (i : I)  → Set
-- μ D i = μ2 D 𝟙 i

-- --The fixed point is actually a fixed point
-- --Thanks to univalence
-- μfix : ∀ {I} {i : I} (D : Desc2 I r) → μ D i ≡ 𝟚 ⊎ FDesc D (μ D) i
-- μfix {i = i} D = ua (isoToEquiv (iso inj emb sec ret))
--  where
--    inj :  μ D i → 𝟚 ⊎ FDesc D (μ D) i
--    inj (init x) = inr x
--    inj μ⁇ = inl true
--    inj μ℧ = inl false
--    emb : 𝟚 ⊎ FDesc D (μ D) i → μ D i
--    emb (inl false) = μ℧
--    emb (inl true) = μ⁇
--    emb (inr x) = init x
--    sec : (b : 𝟚 ⊎ FDesc D (μ D) i)  → _
--    sec (inl false) = refl
--    sec (inl true) = refl
--    sec (inr x) = refl
--    ret : (a : μ D i)  → _
--    ret (init x) = refl
--    ret μ⁇ = refl
--    ret μ℧ = refl


-- -- It's decidable if a μ2 is equal to μ⁇
-- μis℧Bool : ∀ {I r} {i : I} {Unk} {D} → (x : μ2 {r = r} D Unk i) → 𝟚
-- μis℧Bool (init x) = false
-- μis℧Bool μ⁇ = false
-- μis℧Bool μ℧ = true

-- μis℧True : ∀ {I r} {i : I} {Unk} {D} → (x : μ2 {r = r} D Unk i) → μis℧Bool x ≡p true → x ≡ μ℧
-- μis℧True μ℧ eq = refl

-- μis℧False : ∀ {I r} {i : I} {Unk} {D} → (x : μ2 {r = r} D Unk i) → μis℧Bool x ≡p false → ¬ (x ≡ μ℧)
-- μis℧False x bpf eqpf with () ←  true≢false ((cong μis℧Bool (sym eqpf) ∙ (propToPathDec bpf)))

-- μis℧ : ∀ {I} {i : I} {D} {Unk} → (x : μ2 {r = r} D Unk i) → Dec (x ≡ μ℧)
-- μis℧ x with μis℧Bool x in eq
-- ... | true = yes (μis℧True x eq)
-- ... | false = no (μis℧False x eq)

open import GuardedAlgebra

record Datatypes : Set1 where
  field
    numTypes : ℕ
  CName : Set
  CName = Fin numTypes
  field
    numCtors : CName → ℕ
  DName : CName → Set
  DName tyCtor = Fin (numCtors tyCtor)
  field
    -- Each datatye needs to have a Germ defined in terms of strictly positive uses of ⁇
    -- And guarded negative uses of ⁇
    -- We ensure positivity by writing the datatype using a description
    dataGerm : (c : CName) → (▹ Set → DName c → Container 𝟙 )

open Datatypes {{...}} public
