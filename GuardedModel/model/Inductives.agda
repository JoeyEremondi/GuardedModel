

-- Inductive Descriptions for Gradual Datatypes

open import Level
open import Cubical.Data.Nat renaming (Unit to 𝟙)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty renaming (⊥ to 𝟘)
open import Cubical.Relation.Nullary
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Sum as Sum
open import Cubical.Data.FinData
open import Cubical.Data.Bool renaming (Bool to 𝟚)

open import Cubical.Data.Sum
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
open import DecPEq

-- open import Cubical.Data.Bool
open import GuardedAlgebra
import GuardedModality as G

open import ApproxExact
open import Util
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


record ⟦_⟧F {I} (C : Container I) (X : I → Set) (i : I) : Set where
  constructor FC
  field
    command : Command C i
    response :
      (r : Response C command)
      → X (inext C command r)
    -- responseLater :
    --   (r : Response C command)
    --   → ∀ j
    --   → j ≅ inext C command r
    --   → LÆ (X j)
    -- responseUnk : ResponseUnk C command → Unk

-- Functoral action aka good old map
FMap : ∀ {I} {C : Container I} {X Y : I → Set} {i : I} → (∀ {i} → X i → Y i) → ⟦ C ⟧F X i → ⟦ C ⟧F Y i
FMap f (FC com resp) = FC com (λ r → f (resp r))

-- TODO : can't implement the full traversals until we have meet for indices
□ : ∀ {ℓ I} {X : I → Set} (C : Container I) →  ((Σ I X) → Set ℓ) → (Σ I (⟦ C ⟧F X)) → Set ℓ
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
  Wsup : ⟦ C ⟧F  (W̃ C) i → W̃ C i
  W℧ W⁇ : W̃ C i
  -- Projections.

W1 : ∀ {I : Set} (C : Container I) (i : I) → Set
W1 C = ⟦ C ⟧F (W̃ C)

-- head : ∀ {I Unk i} {C : Container I} →  W C Unk i → Command C i
-- head (sup (FC c now later unk)) = c

-- tail : ∀ {I Unk} {C : Container I} {i} (w : W C Unk i) (r : Response C (head w)) → W C Unk (inext C (head w) r)
-- tail {I = I} (sup (_ , _ , k)) r = k r {!!} {!!}

-- --   -- Induction,  (primitive) recursion, and mapping

wInd : ∀ {ℓ} {I } {C : Container I} (P : Σ I (W̃ C) → Set ℓ) →
        (∀ {i} (cs : ⟦ C ⟧F (W̃ C) i) → □ C P (i , cs) → P (i , Wsup cs)) →
        (∀ {i} → P (i , W℧ {i = i})) →
        (∀ {i} → P (i , W⁇ {i = i})) →
        ∀ {i} (w : W̃ C i) → P (i , w)
wInd P φ base℧ base⁇ (Wsup (FC c k)) = φ (FC c k) (λ r → wInd P φ base℧ base⁇ (k r))
wInd P φ base℧ base⁇ W℧ = base℧
wInd P φ base℧ base⁇ W⁇ = base⁇

wRec : ∀ {I } {C : Container I} {X : I → Set} → (∀ {i} → ⟦ C ⟧F (λ i → W̃ C i × X i) i → X i) → (∀ i → X i × X i) → ∀ {i} → W̃ C i → X i
wRec φ base (Wsup (FC c k))= φ (FC c (λ r → (k r , wRec φ base (k r))))
wRec φ base W℧ = fst (base _)
wRec φ base W⁇ = snd (base _)

-- Apply a function at each node in a well-founded tree, bottom-up
-- Basically lifts FMap over the fixed point
everywhere : ∀ {I } {C : Container I} → (∀ {i} → W̃ C i → W̃ C i) → ∀ {i} → W̃ C i → W̃ C i
everywhere f (Wsup (FC com resp)) = Wsup (FC com (λ r → f (everywhere f (resp r))))
everywhere f W℧ = f W℧
everywhere f W⁇ = f W⁇



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


⁇Ref SelfRef : Bool
⁇Ref = false
SelfRef = true

maybeIrrefute : ∀ {A B : Set} {m : Maybe B} → caseMaybe 𝟘 A m → A
maybeIrrefute {m = just x} a = a


maybeIrrefuteUnwrap : ∀ {A B : Set} {m : Maybe B} → caseMaybe 𝟘 A m → B
maybeIrrefuteUnwrap {m = just x} a = x


--TODO update stdlib to have this
Maybe-elim : ∀ {ℓA ℓB} {A : Type ℓA} (B : Maybe A → Type ℓB) → B nothing → ((x : A) → B (just x)) → (mx : Maybe A) → B mx
Maybe-elim B n j nothing = n
Maybe-elim B n j (just a) = j a

-- "Flattened" descriptions. We index by the type that that fields are parameterized over
-- So the shape is never dependent on previous values, only the types
-- We have separate positive and negative "previous" parameters, since
-- the positive ones can't depend on anything behind the guarded modality
data GermCtor : (B : Set) → IndSig → Set1 where
  GEnd : ∀ { B } → GermCtor  B  SigE
  -- Future arguments can only depend on the strictly positive part of the germ
  -- We have a field in GArg of type ⁇ for anything that refers to ⁇ negatively,
  -- but we don't need that in the description itself,
  -- just a bool to denote whether there's negative occurrences of ⁇
  GArg : ∀ {B sig} → (A : B -> Set ) → (D : GermCtor (Σ B A) sig  ) → (hasNeg : Bool) → GermCtor  B (SigA sig)
  GHRec : ∀ {B sig} → (A : B -> Set ) → (D : GermCtor  B sig) → GermCtor  B (SigHR sig)
  GRec : ∀ {B sig} → (D : GermCtor  B sig) → GermCtor  B (SigR sig)
  -- -- Since we don't have Unk in non-germ descriptions specially, it doesn't affect the signature
  -- -- TODO: is this right?
  GUnk : ∀ {B sig} → (A : B -> Set ) → (D : GermCtor  B sig) → GermCtor  B (SigA sig)

GermCommand : ∀  {B sig} → GermCtor B sig → (b : B) → Set
GermCommand GEnd b = Unit
GermCommand (GArg A D _) b  = Σ[ a ∈  A b ] GermCommand D (b , a)
GermCommand (GHRec A D) b  = GermCommand D b
GermCommand (GRec D) b  = GermCommand D b
GermCommand (GUnk A D) b  = GermCommand D b

GermResponse : ∀  {B sig } → (D : GermCtor B sig) → (b : B) → GermCommand D b  → Set
GermResponse {B} GEnd b  com = 𝟘
GermResponse {B} (GArg A D hasNeg) b  (a , com) = GermResponse D (b , a) com
GermResponse {B }  (GHRec A D) b  com =
  -- We have two functions, one for just the positive part, and one for the negative part
  Rec⇒  (A b)
  Rest⇒  (GermResponse D b  com) --TODO: need response to be parameterized by A+ and A- ?
GermResponse {B } (GRec D) b  com = Rec⇒ 𝟙   Rest⇒ GermResponse D b  com
GermResponse {B } (GUnk A D) b  com = GermResponse D b  com


GermResponseUnk : ∀ {B sig } → (D : GermCtor B sig) → (b : B)  → GermCommand D b  → Set
-- Like before, we separate the positive from the negative parts
-- In the "Rest" case, we also need to paramterize by A+ and A- values,
GermResponseUnk  (GUnk A D) b  com =
  Rec⇒ ( A b)
  Rest⇒ ( GermResponseUnk D b  com) --TODO need more here?
GermResponseUnk GEnd b  x = 𝟘
GermResponseUnk (GArg A D hasNeg) b  (a , com) =
-- We only take recursive arguments for Arg if the Arg in the actual data type has negative occurrences of ⁇
   Rec⇒ if hasNeg then 𝟙 else 𝟘 Rest⇒ GermResponseUnk D (b , a) com
GermResponseUnk (GHRec A D) b  com = GermResponseUnk D b  com
GermResponseUnk (GRec D) b  com = GermResponseUnk D b  com

interpGermCtor' : ∀ {A} {B sig } → GermCtor B sig → (b : B) → Container (Maybe A)
interpGermCtor' D b  =
  -- Command encodes any non-recursive parts of datatype
  -- We're only describing uses of ⁇, not defining it, so we don't have commands for when i is false
  (λ i → caseMaybe 𝟘 (GermCommand D b ) i)
  -- The response is either a GermResponse or a GermResponseUnk
  -- Since the functor looks like Σ[ c ∈ Command ]((r : Response com) -> X (inext c r)), the sum is saying
  -- that we have two fields, one with type GermResponse -> X i and one with type GermResponseUnk → X i
  -- The function below encodes that in the first case, X should have index true (self reference)
  -- and in the second case, it should have index False (⁇ reference)
  ◃ (λ {i} com → GermResponse D b  (maybeIrrefute {m = i} com) ⊎ GermResponseUnk D b  (maybeIrrefute {m = i} com) )
  / λ {mTyCtor} com res → Sum.rec
      (λ _ → just (maybeIrrefuteUnwrap {A = GermCommand D b  } com))
      (λ _ → nothing)
      res

interpGermCtor : ∀ {{æ : Æ}} {A} {sig} → GermCtor 𝟙 sig → Set → Container (Maybe A)
interpGermCtor D Self = interpGermCtor'  D tt
-- --
-- -- fs qq


-- toApproxCommand : ∀  {B sig Self} → (D : GermCtor B sig) → (b : B) → ( : -Set B b Self) → GermCommand {Self = Self} D b  → GermCommand {Self = 𝟙} D b {!!}


-- -- -- data IndSig : Set where
-- -- --   SigE SigA SigR SigHR SigU : IndSig

-- -- open import Cubical.Data.List

-- -- data GermDescSig : GermDesc → List IndSig → Set1 where
-- --   GDE : GermDescSig GEnd [ SigE ]
-- --   GDA : ∀ {sig} →  (A : Set) → (D : A → GermDesc) → ((a : A) → GermDescSig (D a) sig) → GermDescSig (GArg A D) (SigA ∷ sig)
-- --   GDHR : ∀ {sig} →  (A : Set) → (D : A → GermDesc) → GermDescSig {!!} {!!}
-- --   GDR : ∀ {sig} →  GermDesc → GermDescSig {!!} {!!}
-- --   GDU : ∀ {sig} →  (A : Set) → GermDesc → GermDescSig {!!} {!!}



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

--TODO: put this in a better spot
--All the data we need from the smaller universe of codes
record SmallerCode : Set1 where
  field
    ℂ-1 : Set
    El-1 : {{æ : Æ}} → ℂ-1 -> Set
    toApprox-1 : (c : ℂ-1) -> El-1 {{æ = Exact}} c → El-1 {{æ = Approx}} c
    toExact-1 : (c : ℂ-1) -> El-1 {{æ = Approx}} c → El-1 {{æ = Exact}} c
    toApproxExact-1 : ∀ {c} {x : El-1 {{æ = Approx }} c} → toApprox-1 c (toExact-1 c x) ≡c x

open SmallerCode public

-- Non-recursive fields in ⁇ for each tag
⁇Args : {{æ : Æ}}
  (smallerCode : SmallerCode)
  → (numCtors : ℕ)
  → TyHead numCtors
  → Set
⁇Args sc numCtors ( HΠ) = 𝟙
⁇Args sc numCtors ( HΣ) = 𝟙
⁇Args sc numCtors ( H≅) = 𝟙
⁇Args sc numCtors ( H𝟙) = 𝟙
⁇Args sc numCtors ( H𝟘) = 𝟘
⁇Args sc numCtors ( HType) = ℂ-1 sc
⁇Args sc numCtors ( HCumul) = Σ (ℂ-1 sc) (El-1 sc)
⁇Args sc numCtors ( (HCtor x)) = 𝟙

-- Roughly "how many" occurrences of ⁇ or DataGerm are fields for each constructor
⁇Resp :
  {{æ : Æ}}
  → (sc : SmallerCode)
  → (numTypes : ℕ)
  → (▹Self : ▹ ⁇Self)
  → (h : TyHead numTypes)
  → ⁇Args sc numTypes h
  → Type
⁇Resp sc numTypes ▹Self HΠ arg = ▹⁇Ty ▹Self
⁇Resp sc numTypes ▹Self HΣ arg = 𝟚
⁇Resp sc numTypes ▹Self H≅ arg = 𝟙
⁇Resp sc numTypes ▹Self H𝟙 arg = 𝟘
⁇Resp sc numTypes ▹Self HType arg =  𝟘
⁇Resp sc numTypes ▹Self HCumul arg =  𝟘
⁇Resp sc numTypes ▹Self (HCtor x) arg = 𝟙

⁇CCommand :
  {{æ : Æ}}
  → (sc : SmallerCode)
  → (numTypes : ℕ)
  → (numCtors : Fin numTypes → ℕ)
  → (sigs : (tyCtor : Fin numTypes) → Fin (numCtors tyCtor) → IndSig)
  → (▹Self : ▹ ⁇Self)
  → (DescFor : (tyCtor : Fin numTypes) → (ctor : Fin (numCtors tyCtor)) → GermCtor 𝟙 (sigs tyCtor ctor) )
  → Maybe (Fin numTypes) → Set
⁇CCommand sc numTypes numCtors sigs ▹Self DescFor =
      -- There's no entry in ⁇ for empty type, so we make sure that its tag isn't ever used
      Maybe.rec
        (Σ[ h ∈ TyHead numTypes ] (⁇Args sc numTypes h))
        (λ tyCtor → Σ[ ctor ∈ Fin (numCtors tyCtor) ] (GermCommand (DescFor tyCtor ctor) tt))

⁇CResp :
  {{æ : Æ}}
  → (sc : SmallerCode)
  → (numTypes : ℕ)
  → (numCtors : Fin numTypes → ℕ)
  → (sigs : (tyCtor : Fin numTypes) → Fin (numCtors tyCtor) → IndSig)
  → (▹Self : ▹ ⁇Self)
  → (DescFor : (tyCtor : Fin numTypes) → (ctor : Fin (numCtors tyCtor)) → GermCtor 𝟙 (sigs tyCtor ctor) )
  → ∀ mTyCtor → ⁇CCommand sc numTypes numCtors sigs ▹Self DescFor mTyCtor → Type
⁇CResp sc numTypes numCtors sigs ▹Self DescFor =
      Maybe-elim (λ m → Maybe.rec _ _ m → Type)
       -- Unk cases
       (λ (h , args) → ⁇Resp sc numTypes ▹Self h args)
       -- DataGerm cases
       -- In DataGerm mode, response is either the response for Self or the response for Unk
       -- i.e. encoding that we have both references to Self and ⁇
       (λ tyCtor (ctor , com)
         → GermResponse (DescFor tyCtor ctor) tt com ⊎ GermResponseUnk (DescFor tyCtor ctor) tt com )

recForHead : ∀ {numTypes} → TyHead numTypes → Maybe _
recForHead (HCtor tyCtor) = just tyCtor
recForHead _ = nothing

-- The inductive structure of ⁇ as a type.
-- We use this to encode positive references to ⁇ inside DataGerm types
-- This should end up being isomorphic to ⁇Ty as defined in Code.agda
⁇Container :
  {{æ : Æ}}
  → (sc : SmallerCode)
  → (numTypes : ℕ)
  → (numCtors : Fin numTypes → ℕ)
  → (sigs : (tyCtor : Fin numTypes) → Fin (numCtors tyCtor) → IndSig)
  → (▹Self : ▹ ⁇Self)
  → (DescFor : (tyCtor : Fin numTypes) → (ctor : Fin (numCtors tyCtor)) → GermCtor 𝟙 (sigs tyCtor ctor) )
  -- Nothing encodes ⁇, just tyCtor encodes the germ for tyCtor
  → Container (Maybe (Fin numTypes))


⁇inext :
  {{æ : Æ}}
  → (sc : SmallerCode)
  → (numTypes : ℕ)
  → (numCtors : Fin numTypes → ℕ)
  → (sigs : (tyCtor : Fin numTypes) → Fin (numCtors tyCtor) → IndSig)
  → (▹Self : ▹ ⁇Self)
  → (DescFor : (tyCtor : Fin numTypes) → (ctor : Fin (numCtors tyCtor)) → GermCtor 𝟙 (sigs tyCtor ctor) )
  → ∀ i → (com : ⁇CCommand sc numTypes numCtors sigs ▹Self DescFor i ) → (resp : ⁇CResp sc numTypes numCtors sigs ▹Self DescFor i com) → Maybe (Fin numTypes)
⁇inext sc numTypes numCtors sigs ▹Self DescFor = Maybe-elim (λ m → (c : ⁇CCommand sc numTypes numCtors sigs ▹Self DescFor m) → ⁇CResp sc numTypes numCtors sigs ▹Self DescFor m c → Maybe (Fin numTypes))
        -- Index for ⁇Case: recursive fields are ⁇ except for ⁇μ case
        (λ (h , _) resp → recForHead h)
        -- In DataGerm, the response tells us whether the field is ⁇ or DataGerm
        (λ tyCtor com resp → Sum.rec (λ _ → just tyCtor) (λ _ → nothing) resp)

⁇Container sc numTypes numCtors sigs ▹Self DescFor
  = (⁇CCommand sc numTypes numCtors sigs ▹Self DescFor) ◃ (⁇CResp sc numTypes numCtors sigs ▹Self DescFor _) / λ {i} c r → ⁇inext sc numTypes numCtors sigs ▹Self DescFor i c r

-- ⁇Container sc numTypes numCtors sigs ▹Self DescFor =
--   let
-- -- -- Functor has form (r : Response c) -> X (inext c r )
-- -- so the response field produces the thing on the LHS of the arrow
-- -- No fields for ⁇⁇ or ⁇℧
--     respT : ∀ mTyCtor → comT mTyCtor → Type
--     respT =
--     -- All references in ⁇ are to ⁇, except for ⁇μ case
--     ix : ∀ i → (com : comT i ) → (resp : respT i com) → Maybe (Fin numTypes)
--     ix = Maybe-elim (λ m → (c : comT m) → respT m c → Maybe (Fin numTypes))
--       -- Index for ⁇Case: recursive fields are ⁇ except for ⁇μ case
--       (λ (h , _) resp → recForHead h)
--       -- In DataGerm, the response tells us whether the field is ⁇ or DataGerm
--       (λ tyCtor com resp → Sum.rec (λ _ → just tyCtor) (λ _ → nothing) resp)
--    in comT ◃ (λ {i} → respT i) / λ {i} → ix i
--         where
--           recForHead : TyHead numTypes → Maybe _
--           recForHead (HCtor tyCtor) = just tyCtor
--           recForHead _ = nothing


-- record DataGerms {{_ : DataTypes}}  : Set1 where
--   field
--     -- Each datatye needs to have a Germ defined in terms of strictly positive uses of ⁇
--     -- And guarded negative uses of ⁇
--     -- We ensure positivity by writing the datatype using a description
--     preDataGerm : ℕ → (c : CName) → ( (d : DName c) → GermCtor 𝟙 (indSkeleton c d) )
--     -- germSig : {{_ : Æ}} → ℕ → (c : CName) → (▹ Set → DName c → GermCtor 𝟙 )
--   preAllDataContainer : {{æ : Æ}} → ℕ → (sc : SmallerCode) → ▹ ⁇Self → Container (Maybe CName)
--   preAllDataContainer {{æ = æ}} ℓ sc ▹Self = (⁇Container sc numTypes numCtors indSkeleton ▹Self λ tyCtor ctor → preDataGerm ℓ tyCtor  ctor)

--   preAllDataTypes : {{æ : Æ}} → ℕ → (sc : SmallerCode) → ▹ ⁇Self → Maybe CName → Set
--   preAllDataTypes ℓ sc ▹Self = W̃ (preAllDataContainer ℓ sc ▹Self)
--   -- germContainer : {{ _ : Æ }} → ℕ → (c : CName) → ▹ Set →  Container 𝟚
--   -- germContainer ℓ c Self  = Arg λ d → interpGermCtor (preDataGerm ℓ c Self d)
--   FPreGerm : {{æ : Æ}} → ℕ → (sc : SmallerCode) → ▹ ⁇Self → CName → Set
--   FPreGerm {{æ = æ}} ℓ sc ▹Self tyCtor  = preAllDataTypes ℓ sc ▹Self (just tyCtor)
--   Pre⁇ : {{_ : Æ}} → ℕ → (sc : SmallerCode) → ▹ ⁇Self → Set
--   Pre⁇ ℓ sc ▹Self  = preAllDataTypes ℓ sc ▹Self nothing

--   -- Traverse a ⁇ structure to switch exact to approx or vice versa
--   ArgToApprox :  ∀ sc (tyHead : TyHead numTypes) → ⁇Args {{æ = Exact}} sc numTypes tyHead → ⁇Args {{æ = Approx}} sc numTypes tyHead
--   ArgToApprox sc HΠ x = x
--   ArgToApprox sc HΣ x = x
--   ArgToApprox sc H≅ x = x
--   ArgToApprox sc H𝟙 x = x
--   ArgToApprox sc HType x = x
--   ArgToApprox sc HCumul (c , x) = c , toApprox-1 sc c x
--   ArgToApprox sc (HCtor x₁) x = x

--   ArgToExact :  ∀ sc (tyHead : TyHead numTypes) → ⁇Args {{æ = Approx}} sc numTypes tyHead → ⁇Args {{æ = Exact}} sc numTypes tyHead
--   ArgToExact sc HΠ x = x
--   ArgToExact sc HΣ x = x
--   ArgToExact sc H≅ x = x
--   ArgToExact sc H𝟙 x = x
--   ArgToExact sc HType x = x
--   ArgToExact sc HCumul (c , x) = c , toExact-1 sc c x
--   ArgToExact sc (HCtor x₁) x = x

--   ArgToApproxExact :  ∀ sc (tyHead : TyHead numTypes) → (x : ⁇Args {{æ = Approx}} sc numTypes tyHead) → ArgToApprox sc tyHead (ArgToExact sc tyHead x) ≡c x
--   ArgToApproxExact sc HΠ x = refl
--   ArgToApproxExact sc HΣ x = refl
--   ArgToApproxExact sc H≅ x = refl
--   ArgToApproxExact sc H𝟙 x = refl
--   ArgToApproxExact sc HType x = refl
--   ArgToApproxExact sc HCumul (x , y) = ΣPathP (refl , toApproxExact-1 sc)
--   ArgToApproxExact sc (HCtor x₁) x = refl

--   ResToApprox :  ∀ {sc} {▹Self tyHead com} → ⁇Resp {{æ = Exact}} sc _ ▹Self tyHead com → ⁇Resp {{æ = Approx}} sc _ tt* tyHead (ArgToApprox sc tyHead com)
--   ResToApprox {tyHead = HΠ} x = tt*
--   ResToApprox {tyHead = HΣ} x = x
--   ResToApprox {tyHead = H≅} x = x
--   ResToApprox {tyHead = HCtor x₁} x = x

--   ResToExact :  ∀ {sc} {▹Self tyHead com} → ⁇Resp {{æ = Approx}} sc _ tt* tyHead (ArgToApprox sc tyHead com) → ⁇Resp {{æ = Exact}} sc _ ▹Self tyHead com
--   ResToExact {tyHead = HΠ} x = ▹⁇⁇ ⦃ æ = Exact ⦄ _
--   ResToExact {tyHead = HΣ} x = x
--   ResToExact {tyHead = H≅} x = x
--   ResToExact {tyHead = HCtor x₁} x = x

--   ResToApproxExact :  ∀ {sc} {▹Self tyHead com} → (x : ⁇Resp {{æ = Approx}} sc _ tt* tyHead (ArgToApprox sc tyHead com)) → ResToApprox {▹Self = ▹Self } (ResToExact x) ≡c x
--   ResToApproxExact {tyHead = HΠ} x = refl
--   ResToApproxExact {tyHead = HΣ} x = refl
--   ResToApproxExact {tyHead = H≅} x = refl
--   ResToApproxExact {tyHead = HCtor x₁} x = refl

--   PreAllToApprox : ∀ {ℓ sc} {Self mI}
--     → preAllDataTypes {{æ = Exact}} ℓ sc Self mI
--     → preAllDataTypes ⦃ æ = Approx ⦄ ℓ sc tt* mI
--   PreAllToApprox W℧ = W℧
--   PreAllToApprox W⁇ = W⁇
--   PreAllToApprox {mI = nothing} (Wsup (FC (h , arg) res)) = Wsup (FC (h , ArgToApprox _ h arg ) λ r → PreAllToApprox (res (ResToExact r)))
--   PreAllToApprox {mI = just tyCtor} (Wsup (FC c res)) = Wsup (FC c λ r → PreAllToApprox (res r))

--   PreAllToExact : ∀ {ℓ sc} {Self mI}
--     → preAllDataTypes {{æ = Approx}} ℓ sc tt* mI
--     → preAllDataTypes ⦃ æ = Exact ⦄ ℓ sc Self mI
--   PreAllToExact {mI = mI} W℧ = W℧
--   PreAllToExact {mI = mI} W⁇ = W⁇
--   PreAllToExact {sc = sc} {Self = Self} {mI = nothing} (Wsup (FC (h , arg) res))
--     = Wsup (FC (h , ArgToExact _ h arg )
--       λ r → PreAllToExact (res (substPath (⁇Resp ⦃ æ = Approx ⦄ sc numTypes tt* h) (ArgToApproxExact sc h arg) (ResToApprox r))))
--   PreAllToExact {mI = just tyCtor} (Wsup (FC c res)) = Wsup (FC c λ r → PreAllToExact (res r))

--   PreAllToApproxExact : ∀ {ℓ sc} {Self mI}
--     → (x : preAllDataTypes {{æ = Approx}} ℓ sc tt* mI)
--     → PreAllToApprox {Self = Self} (PreAllToExact {Self = Self} x) ≡ x
--   PreAllToApproxExact {ℓ = ℓ} {sc = sc} {Self = Self} {mI = nothing} (Wsup (FC (h , arg) resp))
--     = cong₂
--       {A = ⁇Args {{æ = Approx}} sc numTypes h}
--       {B = λ a → (r : Response (preAllDataContainer {{æ = Approx}} ℓ sc tt*) {i = nothing} (h , a)) →
--         W̃ (preAllDataContainer {{æ = Approx}} ℓ sc tt*) (inext (preAllDataContainer {{æ = Approx}} ℓ sc tt*) (h , a) r)}
--       {x = ArgToApprox sc h (ArgToExact sc h arg)}
--       {y = arg}
--       (λ a b → Wsup (FC (h , a) b))
--       (ArgToApproxExact sc h arg)
--       (compEqPath
--         (congP
--           (λ i a →
--             λ (r : Response (preAllDataContainer {{æ = Approx}} ℓ sc tt*) {i = nothing} (h , ArgToApproxExact sc h arg i) )
--               → PreAllToApprox {Self = Self} (PreAllToExact (a r))) rFunEq)
--         (funExtPath (λ r → PreAllToApproxExact {Self = Self} (resp r)))
--         )
--     where
--       sf : ∀ (r' : ⁇Resp {{æ = Approx}} sc numTypes tt* h
--                         (ArgToApprox sc h (ArgToExact sc h arg))) → PathP _ (ResToApprox (ResToExact r')) (substPath (⁇Resp {{æ = Approx}} sc numTypes tt* h)
--                                                                                                (ArgToApproxExact sc h arg) (ResToApprox (ResToExact r')))
--       sf r' = subst-filler  (⁇Resp {{æ = Approx}} sc numTypes tt* h) (ArgToApproxExact sc h arg) (ResToApprox {▹Self = Self} (ResToExact r'))
--       rFunEq : PathP (λ i → (r : Response (preAllDataContainer {{æ = Approx}} ℓ sc tt*) {i = nothing} (h , ArgToApproxExact sc h arg i) ) → preAllDataTypes {{æ = Approx}} ℓ sc tt* (recForHead h) )
--         (λ r →  resp (substPath (⁇Resp {{æ = Approx}} sc numTypes tt* h) (ArgToApproxExact sc h arg) (ResToApprox {▹Self = Self} (ResToExact r))))
--         λ r → resp r
--       rFunEq = symP (toPathP (funExtPath (λ r → {!!})))

--       -- rEq : {!!}
--         -- PreAllToApproxExact {Self = Self} {mI = recForHead h}
--         --   {!!} i
--         --     where
--         --       pf : ∀ {j} → (congPath {B = λ _ → Type} (λ x → ⁇Resp ⦃ æ = Approx ⦄ sc _ tt* h x) {!!}) {!!}  ≡c {!!}

--           -- test : Response (preAllDataContainer {{æ = Approx}} ℓ sc tt*)
--           --     {i = nothing} (h , ArgToApproxExact sc h arg i)
--           --   → Response (preAllDataContainer {{æ = Approx}} ℓ sc tt*)
--           --     {i = nothing }(h , arg)
--           -- test r = transport (congPath {x = ArgToApproxExact sc h arg i} {y = arg}
--           --                       (λ x →
--           --                          Response (preAllDataContainer ⦃ æ = Approx ⦄ ℓ sc tt*) {i = nothing} (h , x))
--           --                       (pathi1 (ArgToApproxExact sc h arg) i)) r

--       -- (toPathP (funExtPath (λ r → {!!} ∙ PreAllToApproxExact (resp r))))
--   PreAllToApproxExact {Self = Self} {mI = just ctor} (Wsup (FC com resp))
--     = congPath {A = typeof resp} {x = λ r → PreAllToApprox {Self = Self} (PreAllToExact (resp r))} {y = resp} (λ x → Wsup {i = just ctor} (FC com x)) (funExtPath (λ r → PreAllToApproxExact (resp r)))
--   PreAllToApproxExact {mI = mI} W℧ = reflc
--   PreAllToApproxExact {mI = mI} W⁇ = refl


-- open DataGerms {{...}} public


-- -- Helpful traversal to get recursion started on an inductive type
-- wRecArg : ∀ {{ _ : DataTypes }} {ℓ} (tyCtor : CName) {I} {C : DName tyCtor → Container I} (P : Set ℓ) →
--         (∀ {i} d (cs : ⟦ (C d) ⟧F (W̃ (Arg C) ) i) → □ (C d) (λ _ → P) (i , cs) → P ) →
--         P →
--         P →
--         ∀ {i} (w : W̃ (Arg C) i) → P

-- wRecArg tyCtor P φ base℧ base⁇ (Wsup (FC (d , c) k)) = φ d (FC c k) (λ r → wRecArg tyCtor P φ base℧ base⁇ (k r))
-- wRecArg tyCtor P φ base℧ base⁇ W℧ = base℧
-- wRecArg tyCtor P φ base℧ base⁇ W⁇ = base⁇
