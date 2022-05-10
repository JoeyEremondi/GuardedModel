

-- Inductive Descriptions for Gradual Datatypes

open import Level
open import Cubical.Data.Nat renaming (Unit to 𝟙)
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (⊥ to 𝟘)
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
module Inductives where


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
  -- ⁇⊢_≅_ : (x y : A ) →   x ≅ y


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
□ : ∀ {ℓ I Unk} {X : I → Set} (C : Container I) →  ((Σ I X) → Set ℓ) → (Σ I (FContainer C X Unk)) → Set ℓ
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

wInd : ∀ {ℓ} {I Unk} {C : Container I} (P : Σ I (W C Unk) → Set ℓ) →
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




data LargeOrd : Set1 where
  LOZ : LargeOrd
  LO↑ : LargeOrd → LargeOrd
  LOLim : (A : Set) → (A → LargeOrd) → LargeOrd

LO1 = LO↑ LOZ



-- Are we providing a recursive argument of a constructor
-- Or the arguments that come after the recursive argument
data Rec⇒_Rest⇒_ (A B : Set) : Set where
  Rec : A → Rec⇒ A Rest⇒ B
  Rest : B → Rec⇒ A Rest⇒ B

--Same as above but for the special code for "under guarded argument"
--We have one case for the description that's under guarded arugment, and one for the rest
data GuardedArg⇒_Rest⇒_ (A B : Set) : Set where
  GuardedArg : A → GuardedArg⇒ A Rest⇒ B
  GRest : B → GuardedArg⇒ A Rest⇒ B

-- "Flattened" descriptions. We index by the type that that fields are parameterized over
-- So the shape is never dependent on previous values, only the types
data GermCtor : Set → Set1 where
  GEnd : ∀ {B} → GermCtor B
  GArg : ∀ {B} → (A : B → Set) → (D : GermCtor (Σ[ b ∈ B ] A b)) → GermCtor B
  GHRec : ∀ {B} → (A : B → Set) → (D : GermCtor B) → GermCtor B
  GRec : ∀ {B} → (D : GermCtor B) → GermCtor B
  GUnk : ∀ {B} → (A : B → Set) → (D : GermCtor B) → GermCtor B

GermCommand : ∀ {B} → GermCtor B → (B → Set)
GermCommand {B} GEnd _ = Unit
GermCommand {B} (GArg A D) b = Σ[ a ∈ A b ] (GermCommand D (b , a))
GermCommand {B} (GHRec A D) b = GermCommand D b
GermCommand {B} (GRec D) b = GermCommand D b
GermCommand {B} (GUnk A D) b = GermCommand D b

GermResponse : ∀ {B} → (D : GermCtor B) → (b : B) → GermCommand D b → Set
GermResponse {B} GEnd b com = 𝟘
GermResponse {B} (GArg A D) b (a , com) = GermResponse D (b , a) com
GermResponse {B} (GHRec A D) b com =  Rec⇒ A b   Rest⇒ (Σ[ a ∈ A b ] GermResponse D b com)
GermResponse {B} (GRec D) b com = Rec⇒ 𝟙   Rest⇒ GermResponse D b com
GermResponse {B} (GUnk A D) b com = GermResponse D b com


GermResponseUnk : ∀ {B} → (D : GermCtor B) → (b : B) → GermCommand D b → Set
GermResponseUnk (GUnk A D) b com = Rec⇒ A b  Rest⇒ (A b × GermResponseUnk D b com)
GermResponseUnk GEnd b x = 𝟘
GermResponseUnk (GArg A D) b (a , com) = GermResponseUnk D (b , a) com
GermResponseUnk (GHRec A D) b com = GermResponseUnk D b com
GermResponseUnk (GRec D) b com = GermResponseUnk D b com

interpGermCtor : ∀ {B} → GermCtor B → B → Container 𝟙
interpGermCtor D b = (λ _ → GermCommand D b) ◃ (GermResponse D b) ◃ (GermResponseUnk D b) / (λ _ _ → tt)



-- data IndSig : Set where
--   SigE SigA SigR SigHR SigU : IndSig

-- open import Cubical.Data.List

-- data GermDescSig : GermDesc → List IndSig → Set1 where
--   GDE : GermDescSig GEnd [ SigE ]
--   GDA : ∀ {sig} →  (A : Set) → (D : A → GermDesc) → ((a : A) → GermDescSig (D a) sig) → GermDescSig (GArg A D) (SigA ∷ sig)
--   GDHR : ∀ {sig} →  (A : Set) → (D : A → GermDesc) → GermDescSig {!!} {!!}
--   GDR : ∀ {sig} →  GermDesc → GermDescSig {!!} {!!}
--   GDU : ∀ {sig} →  (A : Set) → GermDesc → GermDescSig {!!} {!!}



open import GuardedAlgebra

record DataTypes : Set1 where
  field
    numTypes : ℕ
  CName : Set
  CName = Fin numTypes
  field
    numCtors : CName → ℕ
    -- indSig : CName → IndSig
  DName : CName → Set
  DName tyCtor = Fin (numCtors tyCtor)

open DataTypes {{...}} public



record DataGerms {{_ : DataTypes}} : Set1 where
  field
    -- Each datatye needs to have a Germ defined in terms of strictly positive uses of ⁇
    -- And guarded negative uses of ⁇
    -- We ensure positivity by writing the datatype using a description
    dataGerm : {{_ : Æ}} → ℕ → (c : CName) → (▹ Set → DName c → GermCtor 𝟙 )
    -- germSig : {{_ : Æ}} → ℕ → (c : CName) → (▹ Set → DName c → GermCtor 𝟙 )
  germContainer : {{ _ : Æ }} → ℕ → (c : CName) → ▹ Set →  Container 𝟙
  germContainer ℓ c Self  = Arg λ d → interpGermCtor (dataGerm ℓ c Self d) tt
  FGerm : {{ _ : Æ }} → ℕ → (c : CName) → ▹ Set → Set → Set
  FGerm ℓ c Self Unk = W (germContainer ℓ c Self) Unk tt


open DataGerms {{...}} public



wRecArg : ∀ {{ _ : DataTypes }} {ℓ} (tyCtor : CName) {I Unk} {C : DName tyCtor → Container I} (P : Set ℓ) →
        (∀ {i} d (cs : FContainer (C d) (W (Arg C) Unk) Unk i) → □ (C d) (λ _ → P) (i , cs) → P ) →
        P →
        P →
        ∀ {i} (w : W (Arg C) Unk i) → P

wRecArg tyCtor P φ base℧ base⁇ (Wsup (FC (d , c) k u)) = φ d (FC c k u) (λ r → wRecArg tyCtor P φ base℧ base⁇ (k r))
wRecArg tyCtor P φ base℧ base⁇ W℧ = base℧
wRecArg tyCtor P φ base℧ base⁇ W⁇ = base⁇
