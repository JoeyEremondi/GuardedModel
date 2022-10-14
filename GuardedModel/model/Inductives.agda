

-- Inductive Descriptions for Gradual Datatypes

open import Level
open import Cubical.Data.Nat renaming (Unit to 𝟙)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty renaming (⊥ to 𝟘)
open import Cubical.Relation.Nullary
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Maybe
open import Cubical.Data.Sum as Sum
open import Cubical.Data.FinData
open import Cubical.Data.Bool renaming (Bool to 𝟚)

open import Cubical.Data.Sum
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


-- Shamelessly copied from
-- The Agda standard library

infix 5 _◃_/_

record Container (I : Set)  : Set1 where
  constructor _◃_/_
  field
    Command  : (i : I) → Set
    Response : ∀ {i} → Command i → Set
    -- ResponseÆ : ∀ {i} → Command i → Set
    -- ResponseUnk : ∀ {i} → Command i → Set
    inext     : ∀ {i} (c : Command i) → Response c → I

open Container public


-- Given a container for each a : A, produce the new container
-- that is the sum of all those containers.
-- Useful for encoding data constructors encoded as Fin
Arg : ∀ {A I : Set} → (A → Container I) → Container I
Command (Arg {A} f) i = Σ[ a ∈ A ] Command (f a) i
Response (Arg f) (a , com) = Response (f a) com
inext (Arg f) (a , com) r = inext (f a) com r

-- Algebraic operations on containers index types
-- This ends up being useful when we represent all inductives as one giant inductive type
-- which helps with encoding ⁇ as a type
C+ : ∀ {A B} → Container A → Container B → Container (A ⊎ B)
Command (C+ cA cB) = Sum.elim (λ a → Command cA a) (λ b → Command cB b)
Response (C+ cA cB) {inl a} c = Response cA c
Response (C+ cA cB) {inr b} c = Response cB c
inext (C+ cA cB) {inl x} c resp = inl (inext cA c resp)
inext (C+ cA cB) {inr x} c resp = inr (inext cB c resp)

-- Useful for combining containers for different germs into one big one
-- If we have a container for each type constructor indexed by Bool,
-- where false index denotes ⁇ occurrences and true index denotes self reference,
-- produce one giant container where Nothing denotes ⁇ and Just tyCtor denote reference to the nth data type
-- We just ignore the command for the false case, since we are only encoding occurrences of ⁇, not its definition
ContainerCtors : ∀ {n}
  → (Cfor : Fin n → Container Bool)
  → Container (Maybe (Fin n))
Command (ContainerCtors Cfor) nothing = 𝟘
Command (ContainerCtors Cfor) (just tyCtor) = Command (Cfor tyCtor) true
-- Again, we don't specify what ⁇ looks like, just where it occurs
Response (ContainerCtors {n = n} Cfor) {nothing} ()
Response (ContainerCtors Cfor ) {just tyCtor} com = Response (Cfor tyCtor ) com
inext (ContainerCtors Cfor) {nothing} ()
inext (ContainerCtors Cfor) {just tyCtor} com resp =
  if inext (Cfor tyCtor) com resp
  then just tyCtor
  else nothing
-- The semantics ("extension") of an indexed container.
--


record FContainer {I} (C : Container I) (X : I → Set) (i : I) : Set where
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
    -- responseUnk : ResponseUnk C command → Unk




-- TODO : can't implement the full traversals until we have meet for indices
□ : ∀ {ℓ I} {X : I → Set} (C : Container I) →  ((Σ I X) → Set ℓ) → (Σ I (FContainer C X)) → Set ℓ
□ C P (i , (FC c k)) = ∀ r → P (inext C c r , k r)

--   -- Any.

-- ◇ : ∀ {I Unk} {X : I → Set} (C : Container I) → ((Σ I X) → Set) → (Σ I (FContainer C X Unk)) → Set
-- ◇ C P (i , (FC c res u)) = Σ[ r ∈ Response C c ] (P (inext C c r , res r))

-- --Shamelessley copied from
-- -- The Agda standard library
-- --
-- -- Indexed W-types aka Petersson-Synek trees
-- ------------------------------------------------------------------------

-- -- The family of gradual indexed W-types.

data W̃ {I : Set} (C : Container I) (i : I)  :  Set where
  Wsup : FContainer C  (W̃ C) i → W̃ C i
  W℧ W⁇ : W̃ C i
  -- Projections.

W1 : ∀ {I : Set} (C : Container I) (i : I) → Set
W1 C = FContainer C (W̃ C)

-- head : ∀ {I Unk i} {C : Container I} →  W C Unk i → Command C i
-- head (sup (FC c now later unk)) = c

-- tail : ∀ {I Unk} {C : Container I} {i} (w : W C Unk i) (r : Response C (head w)) → W C Unk (inext C (head w) r)
-- tail {I = I} (sup (_ , _ , k)) r = k r {!!} {!!}

-- --   -- Induction, (primitive) recursion and iteration.

wInd : ∀ {ℓ} {I } {C : Container I} (P : Σ I (W̃ C) → Set ℓ) →
        (∀ {i} (cs : FContainer C (W̃ C) i) → □ C P (i , cs) → P (i , Wsup cs)) →
        (∀ {i} → P (i , W℧ {i = i})) →
        (∀ {i} → P (i , W⁇ {i = i})) →
        ∀ {i} (w : W̃ C i) → P (i , w)
wInd P φ base℧ base⁇ (Wsup (FC c k)) = φ (FC c k) (λ r → wInd P φ base℧ base⁇ (k r))
wInd P φ base℧ base⁇ W℧ = base℧
wInd P φ base℧ base⁇ W⁇ = base⁇

wRec : ∀ {I } {C : Container I} {X : I → Set} → (∀ {i} → FContainer C (λ i → W̃ C i × X i) i → X i) → (∀ i → X i × X i) → ∀ {i} → W̃ C i → X i
wRec φ base (Wsup (FC c k))= φ (FC c (λ r → (k r , wRec φ base (k r))))
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


-- Used to classify the "skeleton" of inductive types before we've defined codes
data IndSig : Set where
  SigE : IndSig
  SigA SigR SigHR : IndSig → IndSig

+-Set : (B+ : Set) → (B+ → Set) → Set1
+-Set B+ B- = Σ[ A+ ∈ (B+ → Set) ] ((b : B+) → A+ b → B- b → Set)

⁇Ref SelfRef : Bool
⁇Ref = false
SelfRef = true

-- -- "Flattened" descriptions. We index by the type that that fields are parameterized over
-- -- So the shape is never dependent on previous values, only the types
-- -- We have separate positive and negative "previous" parameters, since
-- -- the positive ones can't depend on anything behind the guarded modality
data GermCtor : (B : Set) → (B → Set) → IndSig → Set1 where
  GEnd : ∀ { B+ B- } → GermCtor B+ B- SigE
  -- Future arguments can only depend on the strictly positive part of the germ
  GArg : ∀ {B+ B- sig} → ((A+ , A-) : +-Set B+ B-) → (D : GermCtor (Σ B+ A+) (λ (b , a) → Σ (B- b) (A- b a)) sig) → GermCtor B+ B- (SigA sig)
  GHRec : ∀ {B+ B- sig} → (A : +-Set B+ B-) → (D : GermCtor B+ B- sig) → GermCtor B+ B- (SigHR sig)
  GRec : ∀ {B+ B- sig} → (D : GermCtor B+ B- sig) → GermCtor B+ B- (SigR sig)
  -- -- Since we don't have Unk in non-germ descriptions specially, it doesn't affect the signature
  -- -- TODO: is this right?
  GUnk : ∀ {B+ B- sig} → (A : +-Set B+ B-) → (D : GermCtor B+ B- sig) → GermCtor B+ B- sig

GermCommand : ∀ {B+ B- sig} → GermCtor B+ B- sig → (b : B+) → (B- b) → Set
GermCommand GEnd b+ b- = Unit
GermCommand (GArg (A+ , A-) D) b+ b- = Σ[ a+- ∈  (Σ[ a+ ∈ A+ b+ ] A- b+ a+ b-) ] GermCommand D (b+ , fst a+-) (b- , snd a+-)
GermCommand (GHRec (A+ , A-) D) b+ b- = GermCommand D b+ b-
GermCommand (GRec D) b+ b- = GermCommand D b+ b-
GermCommand (GUnk (A+ , A-) D) b+ b- = GermCommand D b+ b-

GermResponse : ∀ {B+ B- sig} → (D : GermCtor B+ B- sig) → (b+ : B+) → (b- : B- b+) → GermCommand D b+ b- → Set
GermResponse {B+}{ B- } GEnd b+ b- com = 𝟘
GermResponse {B+}{ B- } (GArg A D) b+ b- ((a+ , a-) , com) = GermResponse D (b+ , a+) (b- , a-) com
GermResponse {B+ }{B- } (GHRec (A+ , A-) D) b+ b- com =
  -- We have two functions, one for just the positive part, and one for the negative part
  Rec⇒  ((A+ b+) ⊎ (Σ[ a+ ∈ A+ b+ ] A- b+ a+ b-))
  Rest⇒  (GermResponse D b+ b- com) --TODO: need response to be parameterized by A+ and A- ?
GermResponse {B+ }{B- } (GRec D) b+ b- com = Rec⇒ 𝟙   Rest⇒ GermResponse D b+ b- com
GermResponse {B+ }{B- } (GUnk A D) b+ b- com = GermResponse D b+ b- com


GermResponseUnk : ∀ {B+ B- sig} → (D : GermCtor B+ B- sig) → (b+ : B+) → (b- : B- b+) → GermCommand D b+ b- → Set
-- Like before, we separate the positive from the negative parts
-- In the "Rest" case, we also need to paramterize by A+ and A- values,
GermResponseUnk (GUnk (A+ , A-) D) b+ b- com =
  Rec⇒ ((A+ b+) ⊎ (Σ[ a+ ∈ A+ b+ ] A- b+ a+ b-))
  Rest⇒ ( GermResponseUnk D b+ b- com) --TODO need more here?
GermResponseUnk GEnd b+ b- x = 𝟘
GermResponseUnk (GArg A D) b+ b- ((a+ , a-) , com) = GermResponseUnk D (b+ , a+) (b- , a-) com
GermResponseUnk (GHRec A D) b+ b- com = GermResponseUnk D b+ b- com
GermResponseUnk (GRec D) b+ b- com = GermResponseUnk D b+ b- com

interpGermCtor' : ∀ {B+ B- sig} → GermCtor B+ B- sig → (b : B+) → B- b → Container Bool
interpGermCtor' D b+ b- =
  -- Command encodes any non-recursive parts of datatype
  -- We're only describing uses of ⁇, not defining it, so we don't have commands for when i is false
  (λ i → if i then GermCommand D b+ b- else 𝟘)
  -- The response is either a GermResponse or a GermResponseUnk
  -- Since the functor looks like Σ[ c ∈ Command ]((r : Response com) -> X (inext c r)), the sum is saying
  -- that we have two fields, one with type GermResponse -> X and one with type GermResponseUnk to X
  -- The function below encodes that in the first case, X should have index true (self reference)
  -- and in the second case, it should have index False (⁇ reference)
  ◃ (λ { {true} com → GermResponse D b+ b- com ⊎ GermResponseUnk D b+ b- com })
  / λ {
      -- Left case: index shoudl be true (self reference)
      {true} com (inl x) → SelfRef
      -- Right case: index should be false  (⁇ reference)
      ; {true} com (inr x) → ⁇Ref
      }

interpGermCtor : ∀ {sig} → GermCtor 𝟙 (λ _ → 𝟙) sig → Container 𝟚
interpGermCtor D = interpGermCtor' D tt tt --interpGermCtor' D tt tt
-- -- data IndSig : Set where
-- --   SigE SigA SigR SigHR SigU : IndSig

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
  field
    indSkeleton : (c : CName) → (DName c) → IndSig

open DataTypes {{...}} public

open import HeadDefs

-- Non-recursive fields in ⁇ for each tag
⁇Args :
  (ℂ-1 : Set)
  → (El-1 : ℂ-1 → Set)
  → (numCtors : ℕ)
  → GHead numCtors
  → Set
⁇Args ℂ-1 El-1 numCtors H⁇ = 𝟙
⁇Args ℂ-1 El-1 numCtors H℧ = 𝟙
⁇Args ℂ-1 El-1 numCtors (HStatic HΠ) = 𝟙
⁇Args ℂ-1 El-1 numCtors (HStatic HΣ) = 𝟙
⁇Args ℂ-1 El-1 numCtors (HStatic H≅) = 𝟙
⁇Args ℂ-1 El-1 numCtors (HStatic H𝟙) = 𝟙
⁇Args ℂ-1 El-1 numCtors (HStatic H𝟘) = 𝟘
⁇Args ℂ-1 El-1 numCtors (HStatic HType) = ℂ-1
⁇Args ℂ-1 El-1 numCtors (HStatic HCumul) = Σ ℂ-1 El-1
⁇Args ℂ-1 El-1 numCtors (HStatic (HCtor x)) = 𝟙

-- The inductive structure of ⁇ as a type.
-- We use this to encode positive references to ⁇ inside DataGerm types
-- This should end up being isomorphic to ⁇Ty as defined in Code.agda
⁇Container :
  {{æ : Æ}}
  → (ℂ-1 : Set)
  → (El-1 : ℂ-1 → Set)
  → (numTypes : ℕ)
  → (numCtors : Fin numTypes → ℕ)
  → (sigs : (tyCtor : Fin numTypes) → Fin (numCtors tyCtor) → IndSig)
  → (▹Self : ▹ Set)
  → (DescFor : (tyCtor : Fin numTypes) → (ctor : Fin (numCtors tyCtor)) → GermCtor 𝟙 (λ _ → 𝟙) (sigs tyCtor ctor))
  -- Nothing encodes ⁇, just tyCtor encodes the germ for tyCtor
  → Container (Maybe (Fin numTypes))
⁇Container ℂ-1 El-1 numTypes numCtors sigs ▹Self DescFor =
  -- There's no entry in ⁇ for empty type, so we make sure that its tag isn't ever used
  (λ { nothing → Σ[ h ∈ GHead numTypes ] (⁇Args ℂ-1 El-1 numTypes h) ; (just tyCtor) → Σ[ ctor ∈ Fin (numCtors tyCtor) ] (GermCommand (DescFor tyCtor ctor) tt tt)})
-- -- Functor has form (r : Response c) -> X (inext c r )
-- so the response field produces the thing on the LHS of the arrow
-- No fields for ⁇⁇ or ⁇℧
  ◃ (λ { {nothing} (H⁇ , _) → 𝟘
    ; {nothing} (H℧ , _) → 𝟘
    -- left of arrow is ▹Self in function case
    ; {nothing} (HStatic HΠ , _) → ▸ ▹Self
    -- Two ⁇ fields in a pair
    ; {nothing} (HStatic HΣ , _) → 𝟚
    -- One witness of ⁇ ≅ ⁇
    ; {nothing} (HStatic H≅ , _) → 𝟙
    -- Don't use H𝟘 as a tag
    ; {nothing} (HStatic H𝟘 , ())
    -- For ⁇μ, there is one field containing the type encoded by the given tyCtor's description
    -- Below, in inext, we specify that it is just tyCtor
    ; {nothing} (HStatic (HCtor x) , _) → 𝟘
    -- Others have no recursive references, so 0 fields
    ; {nothing} (HStatic H𝟙 , _) → 𝟘
    ; {nothing} (HStatic HType , _) → 𝟘
    ; {nothing} (HStatic HCumul , _) → 𝟘
    -- In DataGerm mode, response is either the response for Self or the response for Unk
    -- i.e. encoding that we have both references to Self and ⁇
    ; {just tyCtor} (ctor , com) → GermResponse (DescFor tyCtor ctor) tt tt com ⊎ GermResponseUnk (DescFor tyCtor ctor) tt tt com })
    -- All references in ⁇ are to ⁇, except for ⁇μ case
  / λ { {nothing} (HStatic (HCtor tyCtor) , _) resp → just tyCtor
    ; {nothing} com resp → nothing
    -- Index for inl case encodes that GermResponse describes when we see Self
    ; {just tyCtor} com (inl resp) → just tyCtor
    -- Otherwise, it encodes where we see ⁇
    ; {just tyCtor} com (inr resp) → nothing}


-- Command (⁇Container ℂ-1 El-1 numCtors sigs ▹Self DescFor) nothing = TyHead numCtors
-- Command (⁇Container ℂ-1 El-1 numCtors sigs ▹Self DescFor) (just tyCtor) = GermCommand (DescFor tyCtor) tt tt

-- Response (⁇Container ℂ-1 El-1 numCtors sigs ▹Self DescFor) {nothing} HΠ = {!!}
-- -- Takes a pair of ⁇, 2 -> ⁇ isomorphic to ⁇ × ⁇
-- Response (⁇Container ℂ-1 El-1 numCtors sigs ▹Self DescFor) {nothing} HΣ = 𝟚
-- -- Takes a single witness of type ⁇, witnessing that ⁇ ≅ ⁇
-- Response (⁇Container ℂ-1 El-1 numCtors sigs ▹Self DescFor) {nothing} H≅ = 𝟙
-- -- No fields, head stores enough info
-- Response (⁇Container ℂ-1 El-1 numCtors sigs ▹Self DescFor) {nothing} H𝟙 = 𝟘
-- Response (⁇Container ℂ-1 El-1 numCtors sigs ▹Self DescFor) {nothing} H𝟘 = 𝟘
-- -- Encodes a types from one level smaller
-- Response (⁇Container ℂ-1 El-1 numCtors sigs ▹Self DescFor) {nothing} HType = ℂ-1
-- -- Encodes a value from a type one level smaller
-- Response (⁇Container ℂ-1 El-1 numCtors sigs ▹Self DescFor) {nothing} HCumul = Σ ℂ-1 El-1
-- -- Case corresponding to ⁇μ: encodes a member of the datagerm for the given tyCtor
-- -- So we have a single field, but we specify (below) that its index is just tyCtor
-- Response (⁇Container ℂ-1 El-1 numCtors sigs ▹Self DescFor) {nothing} (HCtor tyCtor) = 𝟙
-- Response (⁇Container ℂ-1 El-1 numCtors sigs ▹Self DescFor) {just tyCtor} com =
--   GermResponse (DescFor tyCtor) tt tt com ⊎ GermResponseUnk (DescFor tyCtor) tt tt com
-- -- Index for HCtor is (just tyCtor), since the field is an element of that dataGerm
-- inext (⁇Container ℂ-1 El-1 numCtors sigs ▹Self DescFor) {nothing} (HCtor tyCtor) _ = just tyCtor
-- -- Indices for all cases except for μ
-- -- If we're in DataGerm mode, then the response specifies both uses of Self and uses of ⁇
-- -- In ⁇ mode, all references except for μ are ⁇ references, not datatype references, so index is nothing
-- inext (⁇Container ℂ-1 El-1 numCtors sigs ▹Self DescFor) {nothing} com resp = nothing
-- -- In DataGerm mode, reference depends on whether response is inl or inr
-- inext (⁇Container ℂ-1 El-1 numCtors sigs ▹Self DescFor) {just x} com resp = {!resp!}


record DataGerms {{_ : DataTypes}} : Set1 where
  field
    -- Each datatye needs to have a Germ defined in terms of strictly positive uses of ⁇
    -- And guarded negative uses of ⁇
    -- We ensure positivity by writing the datatype using a description
    preDataGerm : {{_ : Æ}} → ℕ → (c : CName) → (▹ Set → (d : DName c) → GermCtor 𝟙 (λ _ → 𝟙) (indSkeleton c d) )
    -- germSig : {{_ : Æ}} → ℕ → (c : CName) → (▹ Set → DName c → GermCtor 𝟙 )
  allDataTypes : {{_ : Æ}} → ℕ → (ℂ-1 : Set) → (El-1 : ℂ-1 → Set) → ▹ Set → Maybe CName → Set
  allDataTypes ℓ ℂ-1 El-1 ▹Self = W̃ (⁇Container ℂ-1 El-1 numTypes numCtors indSkeleton ▹Self λ tyCtor ctor → preDataGerm ℓ tyCtor ▹Self ctor)
  -- germContainer : {{ _ : Æ }} → ℕ → (c : CName) → ▹ Set →  Container 𝟚
  -- germContainer ℓ c Self  = Arg λ d → interpGermCtor (preDataGerm ℓ c Self d)
  FPreGerm : {{_ : Æ}} → ℕ → (ℂ-1 : Set) → (El-1 : ℂ-1 → Set) → ▹ Set → CName → Set
  FPreGerm ℓ ℂ-1 El-1 ▹Self tyCtor  = allDataTypes ℓ ℂ-1 El-1 ▹Self (just tyCtor)


open DataGerms {{...}} public



wRecArg : ∀ {{ _ : DataTypes }} {ℓ} (tyCtor : CName) {I} {C : DName tyCtor → Container I} (P : Set ℓ) →
        (∀ {i} d (cs : FContainer (C d) (W̃ (Arg C) ) i) → □ (C d) (λ _ → P) (i , cs) → P ) →
        P →
        P →
        ∀ {i} (w : W̃ (Arg C) i) → P

wRecArg tyCtor P φ base℧ base⁇ (Wsup (FC (d , c) k)) = φ d (FC c k) (λ r → wRecArg tyCtor P φ base℧ base⁇ (k r))
wRecArg tyCtor P φ base℧ base⁇ W℧ = base℧
wRecArg tyCtor P φ base℧ base⁇ W⁇ = base⁇
