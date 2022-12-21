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
    -- How many first-order recursive references a given constructor has
    #FO : (c : CName) → (DName c) →  ℕ
    -- Index of each First-order reference
    -- Nothing is ⁇, Just tyCtor is an element of the germ of tyCtor
    iFO : (c : CName) → (d : DName c) → Fin (#FO c d) → CName

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
    toApproxExact-1 : ∀ c (x : El-1 {{æ = Approx }} c) → toApprox-1 c (toExact-1 c x) ≡c x

open SmallerCode public


record GermCtor {{_ : DataTypes}} : Type1 where
    field
      GermCommand : Type
      GermHOResponse : GermCommand → Type
      iGermHO : (c : GermCommand) → GermHOResponse c → CName
      GermHOUnkResponse : GermCommand → Type

open GermCtor public

record DataGerms {{_ : DataTypes}} : Type1 where
  field
    germCtor : (ℓ : ℕ) → (tyCtor : CName) → (d : DName tyCtor) → GermCtor
  -- Functor
  data ⁇Germ {{æ : Æ}} (ℓ : ℕ)  (sc : SmallerCode) (Self : ▹ ⁇Self) : Maybe CName → Type where
      -- ⁇ and Germ have top and bottom elements
      ⁇℧ : ∀ {i} → ⁇Germ ℓ sc Self i
      ⁇⁇ : ∀ {i} → ⁇Germ ℓ sc Self i
      -- Constructors for ⁇ as a type (i.e index is nothing)
      ⁇𝟙 : ⁇Germ ℓ sc Self nothing
      ⁇ℕ : GNat → ⁇Germ ℓ sc Self nothing
      ⁇Type : {{inst : 0< ℓ}}  → ℂ-1 sc → ⁇Germ ℓ sc Self nothing
      ⁇Cumul : {{inst : 0< ℓ}} → (c : ℂ-1 sc) → El-1 sc c → ⁇Germ ℓ sc Self nothing
      -- This is where ⁇ is a non-positive type: The germ of Π is ⁇ → ⁇
      -- So we need to guard the use of ⁇ in the domain
      ⁇Π : (▹⁇Ty Self  →  ⁇Germ ℓ sc Self nothing) → ⁇Germ ℓ sc Self nothing
      -- The germ of pairs is a pair of ⁇s
      ⁇Σ : (⁇Germ ℓ sc Self nothing  × ⁇Germ ℓ sc Self nothing ) → ⁇Germ ℓ sc Self nothing
      -- The germ of an equality type is a witness of equality between two ⁇s
      -- TODO: is there a way to make the witness approx?
      ⁇≡ : _≅_ {A = ⁇Germ ℓ sc Self nothing} ⁇⁇ ⁇⁇ → ⁇Germ ℓ sc Self nothing
      -- We can embed an element of the germ of any datatype in ⁇
      ⁇μ : (tyCtor : CName) → (x : ⁇Germ ℓ sc Self (just tyCtor)) →  ⁇Germ ℓ sc Self nothing
      -- A member of an inductive type is a constructor, a command for that constructor,
      -- the right number of first-order recursive refs
      -- and a function producing higher order recursive refs
      Wsup : ∀ {tyCtor}
        → (d : DName tyCtor)
        → (com : GermCommand (germCtor ℓ tyCtor d) )
        → (germFO : (n : Fin (#FO tyCtor d)) → ⁇Germ ℓ sc Self (just (iFO tyCtor d n)))
        → (germHO : (r : GermHOResponse (germCtor ℓ tyCtor d) com) → ⁇Germ ℓ sc Self (just (iGermHO (germCtor ℓ tyCtor d) com r)))
        → (germHOUnk : (r : GermHOUnkResponse (germCtor ℓ tyCtor d) com) → ⁇Germ ℓ sc Self nothing)
        → ⁇Germ ℓ sc Self (just tyCtor)

  -- Approximating/embedding for the unknown type
  toApprox⁇ : ∀ {ℓ sc Self i} → ⁇Germ {{æ = Exact}} ℓ sc Self i → ⁇Germ {{æ = Approx}} ℓ sc tt* i
  toExact⁇ : ∀ {ℓ sc Self i} → ⁇Germ {{æ = Approx}} ℓ sc tt* i → ⁇Germ {{æ = Exact}} ℓ sc Self i

  toApprox⁇ ⁇℧ = ⁇℧
  toApprox⁇ ⁇⁇ = ⁇⁇
  toApprox⁇ ⁇𝟙 = ⁇𝟙
  toApprox⁇ (⁇ℕ n) = ⁇ℕ n
  toApprox⁇ (⁇Type x) = ⁇Type x
  toApprox⁇ {sc = sc} (⁇Cumul c x) = ⁇Cumul c (toApprox-1 sc c x)
  -- This is where we really need to approx: we have a guarded function,
  -- so we take its upper limit by giving it ⁇ as an argument
  toApprox⁇ {Self = Self} (⁇Π f) = ⁇Π (λ _ → toApprox⁇ (f (▹⁇⁇ {{æ = Exact}} Self)))
  toApprox⁇ (⁇Σ (x , y)) = ⁇Σ (toApprox⁇ x , toApprox⁇ y)
  toApprox⁇ (⁇≡ (w ⊢ x ≅ y )) = ⁇≡ (toApprox⁇ w ⊢ toApprox⁇ x ≅ toApprox⁇ y)
  toApprox⁇ (⁇μ tyCtor x) = ⁇μ tyCtor (toApprox⁇ x)

  toApprox⁇ (Wsup d com fo ho hoUnk) =
    Wsup
      d
      com
      (λ n → toApprox⁇ (fo n))
      (λ r → toApprox⁇ (ho r))
      (λ r → toApprox⁇ (hoUnk r))

  toExact⁇ ⁇℧ = ⁇℧
  toExact⁇ ⁇⁇ = ⁇⁇
  toExact⁇ ⁇𝟙 = ⁇𝟙
  toExact⁇ (⁇ℕ n) = ⁇ℕ n
  toExact⁇ (⁇Type x) = ⁇Type x
  toExact⁇ {sc = sc} (⁇Cumul c x) = ⁇Cumul c (toExact-1 sc c x)
  -- This is where we really need to approx: we have a guarded function,
  -- so we take its upper limit by giving it ⁇ as an argument
  toExact⁇ (⁇Π f) = ⁇Π (λ _ → toExact⁇ (f tt*))
  toExact⁇ (⁇Σ (x , y)) = ⁇Σ (toExact⁇ x , toExact⁇ y)
  toExact⁇ (⁇≡ (w ⊢ x ≅ y )) = ⁇≡ (toExact⁇ w ⊢ toExact⁇ x ≅ toExact⁇ y)
  toExact⁇ (⁇μ tyCtor x) = ⁇μ tyCtor (toExact⁇ x)
  toExact⁇ (Wsup d com fo ho hoUnk) =
    Wsup
      d
      com
      (λ n → toExact⁇ (fo n))
      (λ r → toExact⁇ (ho r))
      (λ r → toExact⁇ (hoUnk r))

  toApproxExact⁇ :  ∀ {ℓ sc Self i} → ( x : ⁇Germ {{æ = Approx}} ℓ sc tt* i) → toApprox⁇ {Self = Self} (toExact⁇ {Self = Self} x) ≡c x
  toApproxExact⁇ ⁇℧ = refl
  toApproxExact⁇ ⁇⁇ = refl
  toApproxExact⁇ ⁇𝟙 = refl
  toApproxExact⁇ (⁇ℕ n) = refl
  toApproxExact⁇ (⁇Type x) = refl
  toApproxExact⁇ {sc = sc} (⁇Cumul c x) i = ⁇Cumul c (toApproxExact-1 sc c x i)
  toApproxExact⁇ (⁇Π f) = congPath (⁇Π ⦃ æ = Approx ⦄) (funExtPath λ tt → toApproxExact⁇ (f tt*))
  toApproxExact⁇ (⁇Σ (x , y )) = congPath (⁇Σ {{æ = Approx}}) (ΣPathP (toApproxExact⁇ x , toApproxExact⁇ y))
  toApproxExact⁇ (⁇≡ (w ⊢ x ≅ y)) = congPath
                                      (λ x →
                                        ⁇≡ ⦃ æ = Approx ⦄ (x ⊢ ⁇⁇ ⦃ æ = Approx ⦄ ≅ ⁇⁇ ⦃ æ = Approx ⦄))
                                      (toApproxExact⁇ w)
  toApproxExact⁇ (⁇μ tyCtor x) = congS (⁇μ ⦃ æ = Approx ⦄ tyCtor) (toApproxExact⁇ x)
  toApproxExact⁇ {Self = Self} (Wsup d com fo ho hoUnk) i =
    Wsup
      d
      com
      (λ n → toApproxExact⁇ {Self = Self} (fo n) i)
      (λ r → toApproxExact⁇ {Self = Self} (ho r) i)
      (λ r → toApproxExact⁇ {Self = Self} (hoUnk r) i)

open DataGerms {{...}} public
