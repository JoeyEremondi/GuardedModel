{-# OPTIONS --cubical --guarded --lossy-unification #-}

-- Inductive Descriptions for Gradual Datatypes

open import Level
open import Cubical.Data.Nat renaming (Unit to 𝟙)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty renaming (⊥ to 𝟘)
open import Cubical.Relation.Nullary
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Bool renaming (Bool to 𝟚)
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Sum as Sum
open import Cubical.Data.FinData
-- Bool is the gradual unit type, true is tt and false is ℧

open import Cubical.Data.Sum
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
open import DecPEq
open import Cubical.Functions.FunExtEquiv using (funExtDep)

-- open import Cubical.Data.Bool
open import GuardedAlgebra
import GuardedModality as G

open import GTypes

open import ApproxExact
open import Util

open import Constructors

module UnkGerm where



data 0<  : ℕ → Set where
  instance suc< : ∀ {ℓ} → 0< (ℕ.suc ℓ)



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



-- data W̃ {I : Set} (C : Container I) (i : I)  :  Set where
--   Wsup : ⟦ C ⟧F  (W̃ C) i → W̃ C i
--   W℧ W⁇ : W̃ C i
--   -- Projections.

-- W1 : ∀ {I : Set} (C : Container I) (i : I) → Set
-- W1 C = ⟦ C ⟧F (W̃ C)

-- head : ∀ {I Unk i} {C : Container I} →  W C Unk i → Command C i
-- head (sup (FC c now later unk)) = c

-- tail : ∀ {I Unk} {C : Container I} {i} (w : W C Unk i) (r : Response C (head w)) → W C Unk (inext C (head w) r)
-- tail {I = I} (sup (_ , _ , k)) r = k r {!!} {!!}

-- --   -- Induction,  (primitive) recursion, and mapping

-- wInd : ∀ {ℓ} {I } {C : Container I} (P : Σ I (W̃ C) → Set ℓ) →
--         (∀ {i} (cs : ⟦ C ⟧F (W̃ C) i) → □ C P (i , cs) → P (i , Wsup cs)) →
--         (∀ {i} → P (i , W℧ {i = i})) →
--         (∀ {i} → P (i , W⁇ {i = i})) →
--         ∀ {i} (w : W̃ C i) → P (i , w)
-- wInd P φ base℧ base⁇ (Wsup (FC c k)) = φ (FC c k) (λ r → wInd P φ base℧ base⁇ (k r))
-- wInd P φ base℧ base⁇ W℧ = base℧
-- wInd P φ base℧ base⁇ W⁇ = base⁇

-- wRec : ∀ {I } {C : Container I} {X : I → Set} → (∀ {i} → ⟦ C ⟧F (λ i → W̃ C i × X i) i → X i) → (∀ i → X i × X i) → ∀ {i} → W̃ C i → X i
-- wRec φ base (Wsup (FC c k))= φ (FC c (λ r → (k r , wRec φ base (k r))))
-- wRec φ base W℧ = fst (base _)
-- wRec φ base W⁇ = snd (base _)

-- -- Apply a function at each node in a well-founded tree, bottom-up
-- -- Basically lifts FMap over the fixed point
-- everywhere : ∀ {I } {C : Container I} → (∀ {i} → W̃ C i → W̃ C i) → ∀ {i} → W̃ C i → W̃ C i
-- everywhere f (Wsup (FC com resp)) = Wsup (FC com (λ r → f (everywhere f (resp r))))
-- everywhere f W℧ = f W℧
-- everywhere f W⁇ = f W⁇




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





open import HeadDefs

--TODO: put this in a better spot
--All the data we need from the smaller universe of codes
record SmallerCode : Set1 where
  field
    ℂ-1 : Set
    El-1 : {{æ : Æ}} → ℂ-1 -> Set
    toApprox-1 : (c : ℂ-1) -> El-1 {{æ = Exact}} c → El-1 {{æ = Approx}} c
    toExact-1 : (c : ℂ-1) -> El-1 {{æ = Approx}} c → El-1 {{æ = Exact}} c
    toApproxExact-1 : ∀ c (x : El-1 {{æ = Approx }} c) → toApprox-1 c (toExact-1 c x) ≡c x

open SmallerCode public

-- Telescopes of fixed length
-- This is usefl for encoding curried functions of n arguments,
-- so we can ensure that the code version and germ version line up with the right
-- number of arguments
data GermTele : ℕ → Type1 where
  GermNil : GermTele 0
  GermCons : ∀ {n} → (A : Type) → (A → GermTele n ) → GermTele (ℕ.suc n)

GermTeleEnv : ∀ {n} → GermTele n → Type
GermTeleEnv GermNil = 𝟙
GermTeleEnv (GermCons A teleRest) = Σ[ x ∈ A ](GermTeleEnv (teleRest x))

-- "Flattened" descriptions for data Germs.
-- In order to make things terminating, the positive parts of a datatype's germ
-- must all be encoded using the same inductive type.
-- For the negative parts, we have a telescope of domain types,
-- so the types end up working as if constructors had the type (x : Domain) → ⁇Germ i.
-- So we don't have any "commands" like in W types, or indexing:
-- that's erased and/or added back by casts
data GermCtor {{_ : DataTypes}} : IndSig → Set1 where
  -- Terminate a chain of descriptions
  GEnd : GermCtor SigE
  -- Represents non-recursive fields of a constructor.
  -- If we have a field of type (x1 : A1) → ... → (xn : An) → Foo x1 ⋯ xn,
  -- in the germ this is encoded as (x1 : A1) → ... → (xn : An) → ⁇Germ h,
  -- where h is the head of type Foo, or nothing if it's unknown.
  -- This reduces how much loss there is for approximating to ⁇
  GArg : ∀ {sig n} → (A : GermTele n ) → (ixFor : GermTeleEnv A → Maybe TyHead) (D : GermCtor sig  ) → GermCtor  (SigA n sig)
  -- Like arg, but always has the index type that's the same as the datatype, i.e. represents recursive self-reference
  GRec : ∀ {sig n} → (A : GermTele n ) → (D : GermCtor  sig) → GermCtor  (SigR n sig)


-- W-type style translation for dataGerms
-- We don't have any commands, since all fields are shoved into the massive Germ inductive type
-- So we just have a Response
GermResponse : ∀  {{_ : DataTypes}} {sig} →  GermCtor sig → Type
-- 0 pieces of data stored at the end
GermResponse GEnd = 𝟘
-- For arguments or recursive fields, response is whatever type is given by the telescope
GermResponse (GArg A ixFor D) = GermTeleEnv A
GermResponse (GRec A D) = GermTeleEnv A

-- Index for each response of a Germ Constructor
GermIndexFor : ∀ {{_  : DataTypes}} {sig} → (tyCtor : CName) → (D : GermCtor sig) → GermResponse D → Maybe TyHead
GermIndexFor tyCtor (GArg A ixFor D) x = ixFor x
GermIndexFor tyCtor (GRec A D) x = just (HCtor tyCtor)

record DataGerms {{_ : DataTypes}} : Type1 where
  field
    germCtor : (ℓ : ℕ) → (tyCtor : CName) → (d : DName tyCtor) → GermCtor (indSkeleton tyCtor d)
  -- Functor
  data ⁇Germ {{æ : Æ}} (ℓ : ℕ)  (sc : SmallerCode) (Self : ▹ ⁇Self) : Maybe TyHead → Type where
      -- An element of the germ for any head can be embedded into ⁇Ty
      ⁇Tag : ∀ {h} → ⁇Germ ℓ sc Self (just h) → ⁇Germ ℓ sc Self nothing
      -- ⁇ and Germ have top and bottom elements
      ⁇℧ : ⁇Germ ℓ sc Self nothing
      ⁇⁇ : ⁇Germ ℓ sc Self nothing
      -- Constructors for ⁇ as a type (i.e index is nothing)
      ⁇𝟙 : ⁇Germ ℓ sc Self (just H𝟙)
      ⁇ℕ : GNat → ⁇Germ ℓ sc Self (just Hℕ)
      ⁇Type : {{inst : 0< ℓ}}  → ℂ-1 sc → ⁇Germ ℓ sc Self (just HType)
      ⁇Cumul : {{inst : 0< ℓ}} → (c : ℂ-1 sc) → El-1 sc c → ⁇Germ ℓ sc Self (just HCumul)
      -- This is where ⁇ is a non-positive type: The germ of Π is ⁇ → ⁇
      -- So we need to guard the use of ⁇ in the domain
      ⁇ΠA : (æ ≡p Approx) → (𝟙  →  ⁇Germ ℓ sc Self nothing) → ⁇Germ ℓ sc Self (just HΠ)
      ⁇ΠE : (æ ≡p Exact) → (▹⁇Ty Self  → LÆ (⁇Germ ℓ sc Self nothing)) → ⁇Germ ℓ sc Self nothing →  ⁇Germ ℓ sc Self (just HΠ)
      -- The germ of pairs is a pair of ⁇s
      ⁇Σ : (⁇Germ ℓ sc Self nothing  × ⁇Germ ℓ sc Self nothing ) → ⁇Germ ℓ sc Self (just (HΣ))
      -- The germ of an equality type is a witness of equality between two ⁇s
      -- TODO: is there a way to make the witness approx?
      ⁇≡ : _≅_ {A = ⁇Germ ℓ sc Self nothing} ⁇⁇ ⁇⁇ → ⁇Germ ℓ sc Self (just (H≅))
      -- A member of an inductive type is a constructor, a command for that constructor,
      -- the right number of first-order recursive refs
      -- and a function producing higher order recursive refs
      ⁇μ : ∀ {tyCtor}
        → (d : DName tyCtor)
        → ((r : GermResponse (germCtor ℓ tyCtor d)) → ⁇Germ ℓ sc Self (GermIndexFor tyCtor _ r))
        → ⁇Germ ℓ sc Self (just (HCtor tyCtor))

  -- Approximating/embedding for the unknown type
  toApprox⁇ : ∀ {ℓ sc Self i} → ⁇Germ {{æ = Exact}} ℓ sc Self i → ⁇Germ {{æ = Approx}} ℓ sc tt* i
  toExact⁇ : ∀ {ℓ sc Self i} → ⁇Germ {{æ = Approx}} ℓ sc tt* i → ⁇Germ {{æ = Exact}} ℓ sc Self i

  toApprox⁇ ⁇℧ = ⁇℧
  toApprox⁇ ⁇⁇ = ⁇⁇
  toApprox⁇ (⁇Tag x) = ⁇Tag (toApprox⁇ x)
  toApprox⁇ ⁇𝟙 = ⁇𝟙
  toApprox⁇ (⁇ℕ n) = ⁇ℕ n
  toApprox⁇ (⁇Type x) = ⁇Type x
  toApprox⁇ {sc = sc} (⁇Cumul c x) = ⁇Cumul c (toApprox-1 sc c x)
  -- This is where we really need to approx: we have a guarded function,
  -- so we take its upper limit by giving it ⁇ as an argument
  toApprox⁇ {Self = Self} (⁇ΠE _ _ f⁇) = ⁇ΠA reflp (λ _ → toApprox⁇ f⁇)
  toApprox⁇ {Self = Self} (⁇ΠA () f)
  toApprox⁇ (⁇Σ (x , y)) = ⁇Σ (toApprox⁇ x , toApprox⁇ y)
  toApprox⁇ (⁇≡ (w ⊢ x ≅ y )) = ⁇≡ (toApprox⁇ w ⊢ toApprox⁇ x ≅ toApprox⁇ y)
  toApprox⁇ (⁇μ tyCtor f) = ⁇μ tyCtor λ r → toApprox⁇ (f r) --⁇μ tyCtor (toApprox⁇ x)


  toExact⁇ ⁇℧ = ⁇℧
  toExact⁇ ⁇⁇ = ⁇⁇
  toExact⁇ (⁇Tag x) = ⁇Tag (toExact⁇ x)
  toExact⁇ ⁇𝟙 = ⁇𝟙
  toExact⁇ (⁇ℕ n) = ⁇ℕ n
  toExact⁇ (⁇Type x) = ⁇Type x
  toExact⁇ {sc = sc} (⁇Cumul c x) = ⁇Cumul c (toExact-1 sc c x)
  -- This is where we really need to approx: we have a guarded function,
  -- so we take its upper limit by giving it ⁇ as an argument
  toExact⁇ (⁇ΠA _ f) = ⁇ΠE reflp (λ _ → Now (toExact⁇ (f tt))) (toExact⁇ (f tt))
  toExact⁇ (⁇Σ (x , y)) = ⁇Σ (toExact⁇ x , toExact⁇ y)
  toExact⁇ (⁇≡ (w ⊢ x ≅ y )) = ⁇≡ (toExact⁇ w ⊢ toExact⁇ x ≅ toExact⁇ y)
  toExact⁇ (⁇μ tyCtor f) = ⁇μ tyCtor λ r → toExact⁇ (f r)

  toApproxExact⁇ :  ∀ {ℓ sc Self i} → ( x : ⁇Germ {{æ = Approx}} ℓ sc tt* i) → toApprox⁇ {Self = Self} (toExact⁇ {Self = Self} x) ≡c x
  toApproxExact⁇ ⁇℧ = refl
  toApproxExact⁇ ⁇⁇ = refl
  toApproxExact⁇ (⁇Tag x) = cong (⁇Tag {{æ = _}}) (toApproxExact⁇ x)
  toApproxExact⁇ ⁇𝟙 = refl
  toApproxExact⁇ (⁇ℕ n) = refl
  toApproxExact⁇ (⁇Type x) = refl
  toApproxExact⁇ {sc = sc} (⁇Cumul c x) i = ⁇Cumul c (toApproxExact-1 sc c x i)
  -- toApproxExact⁇ (⁇ΠA _ f) = cong₂ (⁇ΠA ⦃ æ = Approx ⦄) (funExtPath λ tt → toApproxExact⁇ (f tt)) ?
  toApproxExact⁇ (⁇ΠA reflp f) = cong₂ (⁇ΠA ⦃ æ = Approx ⦄ ) reflc (funExtPath (λ _ → toApproxExact⁇ (f tt)))
  toApproxExact⁇ (⁇Σ (x , y )) = congPath (⁇Σ {{æ = Approx}}) (ΣPathP (toApproxExact⁇ x , toApproxExact⁇ y))
  toApproxExact⁇ (⁇≡ (w ⊢ x ≅ y)) = congPath
                                      (λ x →
                                        ⁇≡ ⦃ æ = Approx ⦄ (x ⊢ ⁇⁇ ⦃ æ = Approx ⦄ ≅ ⁇⁇ ⦃ æ = Approx ⦄))
                                      (toApproxExact⁇ w)
  toApproxExact⁇ (⁇μ tyCtor x) =  congPath (⁇μ ⦃ æ = _ ⦄ tyCtor) (funExtPath (λ r → toApproxExact⁇ _))

open DataGerms {{...}} public
