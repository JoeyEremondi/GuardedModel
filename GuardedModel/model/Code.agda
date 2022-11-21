{-# OPTIONS --cubical --guarded #-}
-- open import Desc
-- open import Level hiding (#_)
open import Cubical.Data.Nat renaming (Unit to 𝟙)
open import Cubical.Data.Fin hiding (_/_)
open import Cubical.Data.Bool renaming (Bool to 𝟚)
open import Cubical.Data.Empty renaming (⊥ to 𝟘)
open import Cubical.Data.Nat.Order
open import Cubical.HITs.SetQuotients
open import DecPEq
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Inductives
open import Util
open import Cubical.Data.Maybe
open import Cubical.Data.Sum

open import ApproxExact

import GuardedAlgebra as A
import GuardedModality as G
module Code
  {{ _ : DataTypes }}
  {{ _ : DataGerms }}
  where


open import HeadDefs (numTypes)

data 0<  : ℕ → Set where
  instance suc< : ∀ {ℓ} → 0< (suc ℓ)

data Polarity : Set where
  Pos Neg : Polarity

data IsNeg : Polarity → Set where
  isNeg : IsNeg Neg


--Readable datatypes for translating codes into W types

-- -- Are we providing a recursive argument of a constructor
-- -- Or the arguments that come after the recursive argument
-- data Rec⇒_Rest⇒_ (A B : Set) : Set where
--   Rec : A → Rec⇒ A Rest⇒ B
--   Rest : B → Rec⇒ A Rest⇒ B

-- --Same as above but for the special code for "under guarded argument"
-- --We have one case for the description that's under guarded arugment, and one for the rest
-- data GuardedArg⇒_Rest⇒_ (A B : Set) : Set where
--   GuardedArg : A → GuardedArg⇒ A Rest⇒ B
--   GRest : B → GuardedArg⇒ A Rest⇒ B

-- All of the things we access recursively when defining
-- the universe as a guarded fixed-point
-- record SelfRec : Set1 where
--   constructor selfRec
--   field
--     --Recursive references to the type ⁇
--     ⁇Self : Set
--     --The bottom-element of ⁇Self
--     ℧Self : ⁇Self
-- open SelfRec


-- We have each level of codes and ⁇ in its own module
-- So we can then use induction afterwards to build them up from the previous level
record CodeModule
  (ℓ : ℕ)
  : Set (lsuc lzero) where
  field
    sc : SmallerCode
    -- ℂ-1 : Set
    -- El-1 : {{æ : Æ}} → ℂ-1 -> Set
    -- toApprox-1 : (c : ℂ-1) -> El-1 {{æ = Exact}} c → El-1 {{æ = Approx}} c
    -- toExact-1 : (c : ℂ-1) -> El-1 {{æ = Approx}} c → El-1 {{æ = Exact}} c
    -- ⁇-1 : {{_ : Æ}} → Set
    -- ℧-1 : {{_ : 0< ℓ}} →  ℂ-1
    -- ℂSelf : ▹ Set


    ---------------------------------------------------------------------
    ----------- The Unknown Type ----------------------------------------
    -- The Functor describing the unknown type ⁇
    -- We write it as a HIT to make sure all of the error values are equal
  data F⁇ {{ æ : Æ }} (Self : A.▹ ⁇Self) :  Set where
      ⁇℧ : F⁇ Self
      ⁇⁇ : F⁇ Self
      ⁇𝟙 : F⁇ Self
      ⁇Type : {{ inst : 0< ℓ }} → ℂ-1 sc → F⁇ Self
      ⁇Cumul :  {{ inst : 0< ℓ }} → (c : ℂ-1 sc) → El-1 sc c → F⁇ Self
      -- This is where ⁇ is a non-positive type: The germ of Π is ⁇ → ⁇
      -- So we need to guard the use of ⁇ in the domain
      ⁇Π : (▹⁇Ty Self  →  (F⁇ Self )) → F⁇ Self
      -- The germ of pairs is a pair of ⁇s
      ⁇Σ : (F⁇ Self  × F⁇ Self ) → F⁇ Self
      -- The germ of an equality type is a witness of equality between two ⁇s
      -- TODO: is there a way to make the witness approx?
      ⁇≡ : _≅_ {A = F⁇ Self} ⁇⁇ ⁇⁇ → F⁇ Self
      -- TODO: right now, must approximate taking the germ of inductives that use their parameters in dependent ways
      -- e.g. data NotProp A where np : (a b : A) → a ≠ b → NotProp A
      -- It's unclear whether we can use Induction-Induction to do this in a strictly-positive way
      ⁇μ : (tyCtor : CName) → (x : FPreGerm ℓ sc Self tyCtor) →  F⁇ Self
      -- ⁇μ : (tyCtor : CName) → (x : FPreGerm ℓ tyCtor Self (F⁇ Self)) →  F⁇ Self
    -- The unknown type, i.e. the fixed-point of F⁇

  -- Approximating/embedding for the unknown type
  toApprox⁇ : ∀ {Self} → F⁇ {{æ = Exact}} Self  → F⁇ {{æ = Approx}} tt*
  toExact⁇ : ∀ {Self} → F⁇ {{æ = Approx}} tt* → F⁇ {{æ = Exact}} Self

  toApprox⁇ ⁇℧ = ⁇℧
  toApprox⁇ ⁇⁇ = ⁇⁇
  toApprox⁇ ⁇𝟙 = ⁇𝟙
  toApprox⁇ (⁇Type x) = ⁇Type x
  toApprox⁇ (⁇Cumul c x) = ⁇Cumul c (toApprox-1 sc c x)
  -- This is where we really need to approx: we have a guarded function,
  -- so we take its upper limit by giving it ⁇ as an argument
  toApprox⁇ {Self = Self} (⁇Π f) = ⁇Π (λ _ → toApprox⁇ (f (▹⁇⁇ {{æ = Exact}} Self)))
  toApprox⁇ (⁇Σ (x , y)) = ⁇Σ (toApprox⁇ x , toApprox⁇ y)
  toApprox⁇ (⁇≡ (w ⊢ x ≅ y )) = ⁇≡ (toApprox⁇ w ⊢ toApprox⁇ x ≅ toApprox⁇ y)
  toApprox⁇ (⁇μ tyCtor x) = ⁇μ tyCtor (PreAllToApprox x)

  toExact⁇ ⁇℧ = ⁇℧
  toExact⁇ ⁇⁇ = ⁇⁇
  toExact⁇ ⁇𝟙 = ⁇𝟙
  toExact⁇ (⁇Type x) = ⁇Type x
  toExact⁇ (⁇Cumul c x) = ⁇Cumul c (toExact-1 sc c x)
  -- This is where we really need to approx: we have a guarded function,
  -- so we take its upper limit by giving it ⁇ as an argument
  toExact⁇ (⁇Π f) = ⁇Π (λ _ → toExact⁇ (f tt*))
  toExact⁇ (⁇Σ (x , y)) = ⁇Σ (toExact⁇ x , toExact⁇ y)
  toExact⁇ (⁇≡ (w ⊢ x ≅ y )) = ⁇≡ (toExact⁇ w ⊢ toExact⁇ x ≅ toExact⁇ y)
  toExact⁇ (⁇μ tyCtor x) = ⁇μ tyCtor (PreAllToExact x)

  toApproxExact⁇ :  ∀ {Self} → ( x : F⁇ {{æ = Approx}} tt*) → toApprox⁇ {Self = Self} (toExact⁇ {Self = Self} x) ≡c x
  toApproxExact⁇ ⁇℧ = refl
  toApproxExact⁇ ⁇⁇ = refl
  toApproxExact⁇ ⁇𝟙 = refl
  toApproxExact⁇ (⁇Type x) = refl
  toApproxExact⁇ (⁇Cumul c x) = cong (λ x → ⁇Cumul {{æ = Approx}} c x) (toApproxExact-1 sc)
  toApproxExact⁇ (⁇Π f) = congPath (⁇Π ⦃ æ = Approx ⦄) (funExtPath λ tt → toApproxExact⁇ (f tt*))
  toApproxExact⁇ (⁇Σ (x , y )) = congPath (⁇Σ {{æ = Approx}}) (ΣPathP (toApproxExact⁇ x , toApproxExact⁇ y))
  toApproxExact⁇ (⁇≡ (w ⊢ x ≅ y)) = congPath
                                      (λ x →
                                         ⁇≡ ⦃ æ = Approx ⦄ (x ⊢ ⁇⁇ ⦃ æ = Approx ⦄ ≅ ⁇⁇ ⦃ æ = Approx ⦄))
                                      (toApproxExact⁇ w)
  toApproxExact⁇ (⁇μ tyCtor x) = congS (⁇μ ⦃ æ = Approx ⦄ tyCtor) (PreAllToApproxExact x)

  -- Take the fixed point to get the actual type
  ▹⁇Rec : {{æ : Æ}} → A.▹ ⁇Self → ⁇Self
  ▹⁇Rec Self = record { ⁇TySelf = F⁇ Self ; ⁇⁇Self = ⁇⁇ ; ⁇℧Self = ⁇℧ }
  ⁇Rec : {{æ : Æ}} → ⁇Self
  ⁇Rec =  RecFix ▹⁇Rec
  ⁇ : {{æ : Æ}} → Set
  -- ⁇ Is the guarded fixed point of F⁇
  ⁇ = ⁇TySelf ⁇Rec --A.fix F⁇

  interleaved mutual

    ------------------ Declarations ------------------------------
    -- Codes describing types
    data ℂ : Set
    -- Interpretation of codes into types
    El : {{æ : Æ}} → ℂ → Set
    ÆEl : ℂ → ApproxExact.ÆSet0
    ÆEl c æ = El {{æ = æ}} c
    --Approximate type for a code
    ApproxEl : ℂ → Set
    ApproxEl c = El {{Approx}} c
    toApprox : ∀ c → El {{Exact}} c → El {{Approx}} c
    toExact : ∀ c → El {{Approx}} c → El {{Exact}} c
    toApproxExact : ∀ c x → toApprox c (toExact c x) ≡c x
    approx : ∀ {{æ : Æ}} → {c : ℂ} → ÆEl c æ → ApproxEl c
    exact : ∀ {{æ : Æ}} → {c : ℂ} → ApproxEl c → ÆEl c æ
    approx {{Approx}} x = x
    approx {{Exact}} x = toApprox _ x
    exact {{Approx}} x = x
    exact {{Exact}} x = toExact _ x

    -- ApproxedEl : {{æ : Æ}} → ℂ → Set
    -- ApproxedEl {{æ}} c = Approxed (ÆEl c)

    -- Interpretation of codes when they're on the left of an arrow,
    -- used to make the germs of datatypes
    -- ▹El : ℂ → Set
    -- Code-based Descriptions of inductive data types
    data ℂDesc (I : ℂ) : ℂ → IndSig → Set
    -- Interpretation of description codes into W-types
    CommandD : ∀ {{æ : Æ}}  {I cB sig} → ℂDesc I cB sig → ApproxEl I → (ApproxEl cB → Set)
    ResponseD : ∀ {{æ :  Æ}} {I cB sig} → (D : ℂDesc I cB sig) → ∀ {i : ApproxEl I} → (b : ApproxEl cB) → CommandD {{æ = Approx}} D i b → Set
    inextD : ∀  {I cB sig} → (D : ℂDesc I cB sig) → ∀ {i} → (b : ApproxEl cB) → (c : CommandD {{æ = Approx}} D i b) → ResponseD {{æ = Approx}} D b c → ApproxEl  I
    FWUnk : {{_ : Æ}} → A.▹ ⁇Self → Set
    -- ▹interpDesc : ∀{{ _ : Æ }} {I} → (ℂDesc I ) → Container 𝟙
    -- ▹CommandD : ∀ {{ _ : Æ }}{I} →  ℂDesc I  → Set
    -- ▹ResponseD : ∀ {{ _ : Æ }}{I} →  (D : ℂDesc I ) → ▹CommandD D → Set
    toApproxCommandD : ∀  {{æ : Æ}} {I cB sig} → (D : ℂDesc I cB sig) → (i : ApproxEl I) → (b : ApproxEl cB) → CommandD {{æ = æ}} D i b → CommandD {{æ = Approx}} D i b
    -- toApproxCommandDEq : ∀   {I cB sig} → (D : ℂDesc I cB sig) → (i : ApproxEl I) → (b : ApproxEl cB) → (x : CommandD {{æ = Approx}} D i b) → toApproxCommandD {{æ = Approx}} D i b x ≡c x
    toApproxResponseD : ∀ {{æ :  Æ}} {I cB sig} → (D : ℂDesc I cB sig) → ∀ {i : ApproxEl I} → (b : ApproxEl cB) → (com : CommandD {{æ = Approx}} D i b)
      → ResponseD {{æ = æ}} D b com → ResponseD {{æ = Approx}} D b com
    toExactCommandD : ∀   {I cB sig} → (D : ℂDesc I cB sig) → (i : ApproxEl I) → (b : ApproxEl cB) → CommandD {{æ = Approx}} D i b → CommandD {{æ = Exact}} D i b
    toExactResponseD : ∀  {I cB sig} → (D : ℂDesc I cB sig) → ∀ {i : ApproxEl I} → (b : ApproxEl cB) → (com : CommandD {{æ = Approx}} D i b)
      → ResponseD {{æ = Approx}} D b com → ResponseD {{æ = Exact}} D b com
    toApproxExactCommandD : ∀   {I cB sig} → (D : ℂDesc I cB sig) → (i : ApproxEl I) → (b : ApproxEl cB) → (c : CommandD {{æ = Approx}} D i b)
      → toApproxCommandD {{æ = Exact}} D i b (toExactCommandD D i b c) ≡c c
    toApproxExactResponseD : ∀  {I cB sig} → (D : ℂDesc I cB sig) → ∀ {i : ApproxEl I} → (b : ApproxEl cB) → (com : CommandD {{æ = Approx}} D i b)
      → (r : ResponseD {{æ = Approx}} D b com)
      → (toApproxResponseD {{æ = Exact}} D b com (toExactResponseD D b com r) ) ≡c r



    interpDesc : ∀ {{æ : Æ}} {I} {cB} {sig} →  (ℂDesc I cB sig) → ApproxEl cB → Container (ApproxEl I)
    --adapted from https://stackoverflow.com/questions/34334773/why-do-we-need-containers
    interpDesc {{æ = æ}} {I = I} {cB = cB} D b  = (λ i → CommandD {{æ = æ}} D i b) ◃ (λ c → ResponseD {{æ = æ}} D b (toApproxCommandD D _ b c)) / λ {i} c r → inextD D b (toApproxCommandD  D i b c) (toApproxResponseD D b _ r)

    toApproxDesc : ∀ { cI cB sig X Y}
          → (D : ℂDesc cI cB sig)
          → (b : ApproxEl cB)
          → (i : ApproxEl cI)
          → (cs : ⟦ interpDesc {{æ = Exact}} D b ⟧F X i)
          → □ (interpDesc {{æ = Exact}} D b) (λ (j , _) → Y j) (i , cs)
          → ⟦ interpDesc {{æ = Approx}} D b ⟧F Y i
    toExactDesc :
      ∀ { cI cB sig X Y}
          → (D : ℂDesc cI cB sig)
          → (b : ApproxEl cB)
          → (i : ApproxEl cI)
          → (cs : ⟦ interpDesc {{æ = Approx}} D b ⟧F X i)
          → □ (interpDesc {{æ = Approx}} D b) (λ (j , _) → Y j) (i , cs)
          → ⟦ interpDesc {{æ = Exact}} D b ⟧F Y i

    toApproxμ :
      (tyCtor : CName)
        → (cI : ℂ)
        → (cB : ℂ)
        → (D : (d : DName tyCtor) → ℂDesc cI cB (indSkeleton tyCtor d))
        → (i : ApproxEl cI)
        → (b : ApproxEl cB)
        → W̃ (Arg (λ d → interpDesc {{æ = Exact}} (D d) b)) i
        → W̃ (Arg (λ d → interpDesc {{æ = Approx}} (D d) b)) i
    toExactμ :
      (tyCtor : CName)
        → (cI : ℂ)
        → (cB : ℂ)
        → (D : (d : DName tyCtor) → ℂDesc cI cB (indSkeleton tyCtor d))
        → (i : ApproxEl cI)
        → (b : ApproxEl cB)
        → W̃ (Arg (λ d → interpDesc {{æ = Approx}} (D d) b)) i
        → W̃ (Arg (λ d → interpDesc {{æ = Exact}} (D d) b)) i
    toApproxExactμ :
      (tyCtor : CName)
        → (cI : ℂ)
        → (cB : ℂ)
        → (D : (d : DName tyCtor) → ℂDesc cI cB (indSkeleton tyCtor d))
        → (i : ApproxEl cI)
        → (b : ApproxEl cB)
        → (x : W̃ (Arg (λ d → interpDesc {{æ = Approx}} (D d) b)) i )
        → toApproxμ tyCtor cI cB D i b (toExactμ tyCtor cI cB D i b x) ≡c x




    -- toApproxDesc : ∀  {I} {cB} {sig} →  (D : ℂDesc I cB sig) → (b : ApproxEl cB) (i : ApproxEl I) → W̃  (interpDesc {{æ = Exact}} D b) i → W̃  (interpDesc {{æ = Approx}} D b) i
    -- toExactDesc : ∀  {I} {cB} {sig} →  (D : ℂDesc I cB sig) → (b : ApproxEl cB) (i : ApproxEl I) → W̃  (interpDesc {{æ = Approx}} D b) i → W̃  (interpDesc {{æ = Exact}} D b) i
    -- toApproxExactDesc : ∀  {I} {cB} {sig} →  (D : ℂDesc I cB sig) → (b : ApproxEl cB) (i : ApproxEl I) → (x : W̃  (interpDesc {{æ = Approx}} D b) i)
    --   → toApproxDesc D b i (toExactDesc D b i x) ≡ x
    -- toExactDesc : ∀  {I} {cB} {sig} →  (ℂDesc I cB sig) → ApproxEl cB → Container (ApproxEl I)

    ------------------------------- Definitions --------------------

    ----------------------------------------------------------------
    --- Unknown type
    data _ where
      C⁇ : ℂ
    -- The unknown code denotes the unknown type
    El C⁇ = ⁇
    toApprox C⁇ x = toApprox⁇ x
    toExact C⁇ x = toExact⁇ x
    toApproxExact C⁇ x = toApproxExact⁇ x
    -- ▹El C⁇ = G.▹ (⁇ {{Exact}})


    ----------------------------------------------------------------
    --- Error type
    data _ where
      C℧ : ℂ
    -- Failure is the only value of the failure type
    -- However, the code is different from C𝟘 becuase the empty type is consistent with itself
    -- But the failure type is not
    El C℧ = 𝟙
    toApprox C℧ _ = tt
    toExact C℧ _ = tt
    toApproxExact C℧ tt = refl
    -- ▹El C℧ = 𝟙
    ----------------------------------------------------------------
    --- Gradual empty type
    data _ where
      C𝟘 : ℂ
      -- There is no way to embed a value of the empty type into ⁇, except as error
    El C𝟘 = 𝟙
    toApprox C𝟘 x = tt
    toExact C𝟘 x = tt
    toApproxExact C𝟘 tt = refl
    -- ▹El C𝟘 = 𝟙
    ----------------------------------------------------------------
    --- Gradual unit type
    data _ where
      C𝟙 : ℂ
    El C𝟙 = 𝟚
    toApprox C𝟙 x = x
    toExact C𝟙 x = x
    toApproxExact C𝟙 x = refl
    -- ▹El C𝟙 = 𝟚
    ----------------------------------------------------------------
    -- Universes
    -- These are just codes from the level below
    data _ where
      CType : {{ inst : 0< ℓ }} → ℂ
    El CType = ℂ-1 sc
    toApprox CType x = x
    toExact CType x = x
    toApproxExact CType x = refl
    -- ▹El CType = ℂ-1
    --
    --For lower universes, we can lift codes to this universe without needing guardedness
    data _ where
      CCumul :  {{ inst : 0< ℓ }} → ℂ-1 sc → ℂ
      -- ⁇Cumul : ⁇-1 → F⁇ Self
    El (CCumul c) = El-1 sc c
    toApprox (CCumul c) x = toApprox-1 sc c x
    toExact (CCumul c) x = toExact-1 sc c x
    toApproxExact (CCumul c) x = toApproxExact-1 sc
    --
    -----------------------------------------------------------------
    -- Codes can "eat themselves" and have a code denoting the set of all codes
    -- So long as we hide it behind the guarded modality
    -- data _ where
    --   CTypeSelf : ℂ
    --   ⁇TypeSelf : ▸ ℂSelf → F⁇ Self
    -- El CTypeSelf = ▸ ℂSelf

    --For lower universes, we can lift codes to this universe without needing guardedness
    -- data _ where
    --   CCumul : ℂ-1 → ℂ
    --   ⁇Cumul : ⁇-1 → F⁇ Self
    -- El (CCumul c) = El-1 c

    ----------------------------------------------------------------
    --- Gradual functions
    --- This is where we capture the possibility for non-termination (in the guarded version)
    --- For approx-norm, L A = A
    data _ where
      CΠ : (dom :  ℂ) → (cod : (x : ApproxEl dom ) → ℂ) → ℂ


    El (CΠ dom cod) = (x : El dom) → (El (cod  (approx x)))
    toApprox (CΠ dom cod) f = λ x → toApprox (cod (approx ⦃ Approx ⦄ {dom} x)) (subst (λ y → ÆEl (cod y) Exact) (toApproxExact dom x) (f (toExact dom x)))
    toExact (CΠ dom cod) f = λ x → toExact (cod (approx ⦃ Exact ⦄ {dom} x)) (f (toApprox dom x))
    toApproxExact (CΠ dom cod) f = funExt λ x →
      JPath
        (λ y pf → toApprox _ (substPath (λ z → ÆEl (cod z) Exact) pf (toExact (cod (toApprox dom (toExact dom x))) (f (toApprox dom (toExact dom x))))) ≡c f y)
        (congPath (toApprox (cod (toApprox dom (toExact dom x)))) (substRefl (toExact (cod (toApprox dom (toExact dom x)))
                                                                               (f (toApprox dom (toExact dom x))))) ∙ toApproxExact (cod (toApprox dom (toExact dom x))) (f (toApprox dom (toExact dom x))))
        (toApproxExact dom x)
 -- toApprox (cod x)
 --      (substPath (λ y → ÆEl (cod y) Exact) (toApproxExact dom x)
 --       (toExact (cod (toApprox dom (toExact dom x)))
 --        (f (toApprox dom (toExact dom x)))))
 --      ≡c f x

    -- Notation for non-dep functions
    _C→_ : ℂ → ℂ → ℂ
    a C→ b = CΠ a (λ _ → b)

    ----------------------------------------------------------------
    --- Gradual pairs
    data _ where
      CΣ : (dom :  ℂ) → (cod : (x : ApproxEl dom ) → ℂ) → ℂ
      --TODO: is it only error if BOTH are error?
    El (CΣ dom cod) = Σ[ x ∈ El dom ]( El (cod (approx x)) )
    toApprox (CΣ dom cod) (x , y) = toApprox dom x , toApprox _ y
    toExact (CΣ dom cod) (x , y) = toExact dom x , toExact (cod (toApprox dom (toExact dom x))) (substPath (λ z → ApproxEl (cod z)) (sym (toApproxExact dom x)) y)
    toApproxExact (CΣ dom cod) (x , y) = ΣPathP (toApproxExact dom x , λ i → toApproxExact (cod _) (pth2 i) i )
      where
        pth2 : PathP (λ i → ApproxEl (cod (toApproxExact dom x i)))
            (substPath (λ z → ApproxEl (cod z))
            (λ i → toApproxExact dom x (~ i)) y)
          y
        pth2 = symP (subst-filler (λ z → ApproxEl (cod z)) (λ i → toApproxExact dom x (~ i)) y)

    -- JDep
    --                                                                      (λ xx eq yy pth →
    --                                                                         PathP (λ i → ApproxEl (cod (eq i)))
    --                                                                         (toApprox (cod (toApprox dom (toExact dom x)))
    --                                                                          (toExact (cod (toApprox dom (toExact dom x)))
    --                                                                           (substPath (λ z → ApproxEl (cod z))
    --                                                                            (sym eq) yy)))
    --                                                                         yy)
    --                                                                      {!!} (toApproxExact dom x) λ i → substPath {!!} {!!} y)
    -- toApproxExact (CΣ dom cod) (x , y) = ΣPathP (toApproxExact dom x , toPathP (JPath (λ yy eq → toExact (cod (toApprox dom (toExact dom x))) (subst (λ z → ApproxEl (cod z)) eq) yy ≡c y) {!!} (toApproxExact dom x)))
    -- ▹El (CΣ dom cod) = Σ[ x ∈ ▹El dom ]( ▹El (cod (inr x)) )
    -- Notation for non-dep pairs
    _C×_ : ℂ → ℂ → ℂ
    a C× b = CΣ a (λ _ → b)

    --- Gradual propositional equality i.e. witnesses of consistency
    data _ where
      C≡ : (c :  ℂ) → (x y : ApproxEl c) → ℂ
    El (C≡ c x y) = x ≅ y
    toApprox (C≡ c x y) pf = pf
    toExact (C≡ c x y) pf = pf
    toApproxExact (C≡ c x y) pf = refl
    -- ▹El (C≡ c x y) = ▹El c
    ----------------------------------------------------------------
    --- Gradual inductive types
    ---


    data _ where
      Cμ :
        (tyCtor : CName)
        → (cI : ℂ)
        → (D : (d : DName tyCtor) → ℂDesc cI C𝟙 (indSkeleton tyCtor d))
        → ApproxEl cI
        → ℂ
    El (Cμ tyCtor cI D i) = W̃ (Arg (λ d → interpDesc (D d) true)) i
    -- toApprox (Cμ tyCtor cI Ds iStart) (Wsup (FC (d , com) res)) =
    --   with (FC retCom retRes) ← toApproxDesc {Y = λ j → {!!}} (Ds d) true {!!} (FC com res) (λ r → {!!})
    --   = {!x!}
    -- toApprox (Cμ tyCtor cI Ds iStart) W⁇ = W⁇
    -- toApprox (Cμ tyCtor cI Ds iStart) W℧ = W℧
    toApprox (Cμ tyCtor cI Ds iStart) x = toApproxμ tyCtor cI C𝟙 Ds iStart true x
    toExact (Cμ tyCtor cI Ds iStart) x = toExactμ tyCtor cI C𝟙 Ds iStart true x
    toApproxExact (Cμ tyCtor cI Ds i) x = toApproxExactμ tyCtor cI C𝟙 Ds i true x

    -- cong (λ (FC com resp) → Wsup (FC (d , com) resp)) recEq
    --   where
    --     recEq = toApproxExactDesc tyCtor cI _ Ds iStart b (Ds d) b _ (FC com resp)


    -- We then take the quotient of ⁇ by a relation defining errors at each of the germ types
    -- This is so casting from ⁇ to a type, and then back, always produces ℧

    -- -- Path constructors for F⁇
    -- data F⁇ where
    --   -- All error values are equal
    --   ⁇℧≡ : ∀ (x : F⁇ Self {true}) → ℧≡ x → ⁇℧ ≡ x
    --   -- All equalities are equal
    --   ⁇IsSet : ∀ (x y : F⁇ Self {true}) → (p1 p2 : x ≡ y) → p1 ≡ p2
      -- ⁇⊥≡ : ∀ x

--     ----------------------------------------------------------------------



    ----------------------------------------------------------------------
    -- Codes for descriptions of inductive types
    data ℂDesc  where
      CEnd : ∀ {cB} → (i : ApproxEl  I) → ℂDesc I cB SigE
      CArg : ∀ {cB} {rest} → (c : ApproxEl cB → ℂ) → (D : ℂDesc I (CΣ cB c) rest) → (cB' : ℂ) → ((CΣ cB c) ≡p cB') → ℂDesc  I cB (SigA rest)
      CRec : ∀ {cB} {rest} (j :  ApproxEl I) → (D :  ℂDesc I cB rest) → ℂDesc I cB (SigR rest)
      CHRec : ∀ {cB} {rest} → (c : ApproxEl cB → ℂ) → (j : (b : ApproxEl cB) → ApproxEl (c b) → ApproxEl I) → (D : ℂDesc I cB rest)
        → (cB' : ℂ) → ((CΣ cB c) ≡p cB')
        → ℂDesc I cB (SigHR rest)

    -- interpDesc D b  = CommandD D b  ◃ ResponseD  D  b  ◃  (λ _ → 𝟘) / inextD D b

    CommandD (CEnd j) i b = i ≅ j
    CommandD (CArg c D _ _) i b = Σ[ a ∈ El (c b) ] CommandD D i (b , approx a)
    CommandD (CRec j D) i b = CommandD D i b
    CommandD (CHRec c j D _ _) i b = CommandD D i b
--     -- CommandD (CHGuard c D E) i =  ((▹ (El c)) → CommandD D i) × CommandD E i

    ResponseD (CEnd i) b com = 𝟘
    ResponseD (CArg c D _ _) b (a , com) = ResponseD D (b , a) com
    ResponseD (CRec j D) b com = Rec⇒ 𝟙    Rest⇒ (ResponseD D b com)
    ResponseD (CHRec c j D _ _) b com = Rec⇒ (El (c b) )    Rest⇒ (ResponseD D b com)
    -- ResponseD (CHGuard c D E) (comD , comE) =
    --   GuardedArg⇒ (Σ[ a▹ ∈  ▹ El c ] (ResponseD D (comD a▹)))
    --     Rest⇒ ResponseD E comE


    inextD (CArg c D _ _) {i} b (a , com) res = inextD D (b ,  a) com res
    inextD (CRec j D) {i} b com (Rec x) = j
    inextD (CRec j D) {i} b com (Rest x) = inextD D b com x
    inextD (CHRec c j D _ _) {i} b com (Rec res) = j b (res)
    inextD (CHRec c j D _ _) {i} b com (Rest res) = inextD D b com res
    -- inextD (CHGuard c D D₁) {i} (f , com) (GuardedArg (a , res)) = inextD D (f a) res
    -- inextD (CHGuard c D D₁) {i} (a , com) (GRest x) = inextD D₁ com x


    -- ▹interpDesc {I = I} D = (λ _ → ▹CommandD D) ◃ ▹ResponseD D  ◃  (λ _ → 𝟘) / λ _ _ → tt

    -- ▹CommandD (CEnd j) = 𝟙
    -- ▹CommandD (CArg c D) = Σ[ a ∈ ▹El c ] ▹CommandD (D (inr a))
    -- ▹CommandD (CRec j D) = ▹CommandD D
    -- ▹CommandD (CHRec c j D) = (a : ▹El c) → ▹CommandD (D (inr a))
    -- -- CommandD (CHGuard c D E) i =  ((▹ (El c)) → CommandD D i) × CommandD E i

    -- ▹ResponseD (CEnd i) com = 𝟘
    -- ▹ResponseD (CArg c D) (a , com) = ▹ResponseD (D (inr a)) com
    -- ▹ResponseD (CRec j D) com = Rec⇒ 𝟙    Rest⇒ (▹ResponseD D com)
    -- ▹ResponseD (CHRec c j D) com = Rec⇒ El c    Rest⇒ (Σ[ a ∈ ▹El c ] ▹ResponseD (D (inr a)) (com a))
    --
    --
    --
    FWUnk Self = Pre⁇ ℓ sc Self

    toApproxCommandD {{æ = Approx}} D i b com = com
    toApproxCommandD (CEnd i₁) i b com = com
    toApproxCommandD (CArg c D cB' x) i b (a , com) = approx  {c = c b}  a , toApproxCommandD D i (b , approx {c = c b} a) com
    toApproxCommandD (CRec j D) i b com = toApproxCommandD D i b com
    toApproxCommandD (CHRec c j D cB' x) i b com = toApproxCommandD D i b com

    toApproxResponseD {{æ = Approx}} D b com r = r
    toApproxResponseD (CArg c D cB' x) b com r = toApproxResponseD D (b , (fst com)) (snd com) r
    toApproxResponseD (CRec j D) b com (Rec x) = Rec tt
    toApproxResponseD (CRec j D) b com (Rest r) = Rest (toApproxResponseD D b _ r)
    toApproxResponseD (CHRec c j D cB' x) b com (Rec r) = Rec (approx {c = (c b)} r)
    toApproxResponseD (CHRec c j D cB' x) b com (Rest r) = Rest (toApproxResponseD D b _ r)

    toExactCommandD (CEnd i₁) i b com = com
    toExactCommandD (CArg c D cB' x) i b (a , com) = toExact (c b) a , toExactCommandD D i (b , _) (substPath (λ a → CommandD ⦃ æ = Approx ⦄ D i (b , a)) (symPath (toApproxExact (c b) a)) com)
    toExactCommandD (CRec j D) i b com = toExactCommandD D i b com
    toExactCommandD (CHRec c j D cB' x) i b com = toExactCommandD D i b com

    toExactResponseD (CArg c D cB' x) b com r = toExactResponseD D (b , (fst com)) (snd com) r
    toExactResponseD (CRec j D) b com (Rec x) = Rec tt
    toExactResponseD (CRec j D) b com (Rest r) = Rest (toExactResponseD D b _ r)
    toExactResponseD (CHRec c j D cB' x) b com (Rec r) = Rec (toExact (c b) r)
    toExactResponseD (CHRec c j D cB' x) b com (Rest r) = Rest (toExactResponseD D b _ r)

    toApproxExactCommandD (CEnd i₁) i b com = refl
    toApproxExactCommandD (CArg c D cB' x) i b (a , com) =
      ΣPathP
        (toApproxExact (c b) a
        , compPathEq (congP (λ _ x → toApproxCommandD ⦃ æ = Exact ⦄ D _ _ (toExactCommandD D _ _ x )) pth) (toApproxExactCommandD D i _ com))
      where
        pth = symP (subst-filler (λ v → CommandD {{æ = _}} D i (b , v)) (λ i₁ → toApproxExact (c b) a (~ i₁)) com)
    toApproxExactCommandD (CRec j D) i b com = toApproxExactCommandD D i b com
    toApproxExactCommandD (CHRec c j D cB' x) i b com = toApproxExactCommandD D i b com

    toApproxExactResponseD (CArg c D cB' x) b com r = toApproxExactResponseD D _ (snd com) r
    toApproxExactResponseD (CRec j D) b com (Rec tt) = refl
    toApproxExactResponseD (CRec j D) b com (Rest r) = congPath Rest (toApproxExactResponseD D b com r)
    toApproxExactResponseD (CHRec c j D cB' x) b com (Rec r) = congPath Rec (toApproxExact (c b) r)
    toApproxExactResponseD (CHRec c j D cB' x) b com (Rest r) = congPath Rest (toApproxExactResponseD D b com r)


--     {-# BUILTIN REWRITE _≡_ #-}
--     {-# REWRITE toApproxExactResponseD toApproxExactCommandD #-}

    toApproxDesc {Y = Y} D b i (FC com res) φ =
      FC
        (toApproxCommandD ⦃ æ = Exact ⦄ D i b com)
        λ r →
          let
            ret = φ (toExactResponseD D b (toApproxCommandD ⦃ Exact ⦄ {_} {_} {_} D i b com) r)
          in transport {!com!} (φ {!!}) --transport (cong₂ (λ c r → Y (inextD D b c r)) refl (toApproxExactResponseD D b _ r)) ret

--     toExactDesc {Y = Y} D b i (FC com res) φ =
--       FC (toExactCommandD D i b com)
--       λ r →
--           let
--             ret = φ (toApproxResponseD ⦃ æ = Exact ⦄ D b _ (transport (congPath (ResponseD ⦃ æ = _ ⦄ D b) (toApproxExactCommandD D i b com)) r))
--           in transport (cong₂ (λ c r → Y (inextD D b c (toApproxResponseD {{æ = Exact}} D b c r))) (symPath (toApproxExactCommandD D i b com)) (symP (toPathP refl))) ret

--     open import Cubical.Functions.FunExtEquiv using (funExtDep)
--     -- toApproxExactDesc :
--     --   ∀ { cI cB sig X Y}
--     --     → (D : ℂDesc cI cB sig)
--     --     → (b : ApproxEl cB)
--     --     → (i : ApproxEl cI)
--     --     → (cs @ (FC com resp) : ⟦ interpDesc {{æ = Approx}} D b ⟧F X i)
--     --     → (φ : □ (interpDesc {{æ = Approx}} D b) (λ (j , _) → Y j) (i , cs))
--     --     → toApproxDesc {X = Y} D b i (toExactDesc D b i cs φ )
--     --                    (λ r →
--     --                      let

--     --                        respr = resp (toApproxResponseD ⦃ æ = Exact ⦄ D b (⟦_⟧F.command cs) (subst (ResponseD {{æ = _}} D b) (toApproxExactCommandD D i b (com)) r))
--     --                      in {!respr!}
--     --                    )

--     --       ≡c cs
-- --     toApproxExactDesc {X = X} {Y = Y} D b ix (FC com resp) φ = cong₂ FC (toApproxExactCommandD D ix _ com)
-- --       (funExtDep (λ {r1} {r2} p → helper r1 r2 p ))
-- --       where
-- --         lx : (r1 : _) → _
-- --         lx r1 =
-- --                 resp
-- --                 (toApproxResponseD {{æ = Exact}} D b com
-- --                   (substPath (ResponseD {{æ = Exact}} D b) (toApproxExactCommandD D ix b com)
-- --                   (toExactResponseD D b
-- --                     (toApproxCommandD {{æ = Exact}} D ix b
-- --                     (⟦_⟧F.command {X = Y} (toExactDesc {X = X} D b ix (FC com resp) φ)))
-- --                     r1)))
-- --         eq1 : (r1 : _) → _
-- --         eq1 r1 i =
-- --                   X
-- --                   (inextD D b
-- --                   (toApproxCommandD {{æ = Exact}} D ix b
-- --                     (⟦_⟧F.command {X = Y} (toExactDesc {X = X} D b ix (FC com resp) φ)))
-- --                   (toApproxExactResponseD D b
-- --                     (toApproxCommandD {{æ = Exact}} D ix b
-- --                       (⟦_⟧F.command {X = Y} (toExactDesc D b ix (FC com resp) φ)))
-- --                     r1 i))
-- --         eq2 : (r1 : _) →  _
-- --         eq2 r1 i =
-- --                   X
-- --                   (inextD D b (symPath (toApproxExactCommandD D ix b com) i)
-- --                   (toApproxResponseD {{æ = Exact}} D b
-- --                     (symPath (toApproxExactCommandD D ix b com) i)
-- --                     (symP {A = λ i → (congPath (ResponseD {{æ = Exact}} D b) (toApproxExactCommandD D ix b com)) (~ i) }
-- --                     (transport-filler
-- --                       (congPath (ResponseD {{æ = Exact}} D b) (toApproxExactCommandD D ix b com))
-- --                       (toExactResponseD D b
-- --                       (toApproxCommandD {{æ = Exact}} D ix b
-- --                         (⟦_⟧F.command {X = Y} (toExactDesc {X = X} D b ix (FC com resp) φ)))
-- --                       r1))
-- --                     i)))
-- --         helper : (r1 : ResponseD ⦃ æ = Approx ⦄ D b (toApproxCommandD {{æ = Exact}} D ix b (toExactCommandD D ix b com)))
-- --           → (r2 : ResponseD {{æ = Approx}} D b com)
-- --           → (p : PathP
-- --               (λ i →
-- --                 ResponseD ⦃ æ = Approx ⦄ D b (toApproxExactCommandD D ix b com i))
-- --               r1 r2) → PathP (λ i →
-- --                                 X
-- --                                 (inextD D b (toApproxExactCommandD D ix b com i) (p i)))
-- --                             (transport (eq1 r1) (transport (eq2 r1) (lx r1)))
-- --                             (resp r2)
-- --         helper r1 r2 p = compEqPath (sym (transportComposite _ _ _)) helperComp
-- --           where
-- --             helperPath : PathP (λ i →  (eq2 r1 ∙ eq1 r1) (~ i)) (transportPath ( (eq2 r1) ∙ (eq1 r1)) (lx r1)) (lx r1)
-- --             helperPath = symP (transport-filler (eq2 r1 ∙ eq1 r1) (lx r1) )
-- --             -- helperPath' : (r1 : ResponseD ⦃ æ = Approx ⦄ D b (toApproxCommandD {{æ = Exact}} D ix b (toExactCommandD D ix b com)))
-- --             --   → (r2 : ResponseD {{æ = Approx}} D b com)
-- --             --   → (p : PathP
-- --             --       (λ i →
-- --             --          ResponseD ⦃ æ = Approx ⦄ D b (toApproxExactCommandD D ix b com i))
-- --             --       r1 r2)
-- --             --       → PathP (λ j → compPath (λ i → compPath (eq2 r1) (eq1 r1) (~ i)) {!!} j)
-- --             --           (transportPath (compPath (eq2 r1) (eq1 r1)) (lx r1)) {!!}
-- --             -- helperPath' r1 r2 p =  compPathP {A = λ i → compPath (eq2 r1) (eq1 r1) (~ i)} {B_i1 = {!!}} {B = {!!}} (helperPath r1 r2 p) {!!}
-- --             r12Path : (toApproxResponseD {{æ = Exact}} D b com
-- --                 (substPath (ResponseD {{æ = Exact}} D b) (toApproxExactCommandD D ix b com)
-- --                 (toExactResponseD D b
-- --                 (toApproxCommandD {{æ = Exact}} D ix b
-- --                 (toExactCommandD D ix b com))
-- --               r1))) ≡c r2
-- --             r12Path = ? -- congPath (toApproxResponseD ⦃ æ = Exact ⦄ D b com) (subLemma (ResponseD {{æ = _}} D b) (λ c → toExactResponseD D b c {!!}) (toApproxExactCommandD D ix b com)) ∙ {!!}

-- --             helperLx : PathP (λ i → X (inextD D b com (r12Path i)))
-- --                                 (lx r1)
-- --                                 (resp r2)
-- --             helperComp : PathP (λ i →
-- --                                     X
-- --                                     (inextD D b (toApproxExactCommandD D ix b com i) (p i)))
-- --                                 (transport (eq2 r1 ∙ eq1 r1) (lx r1))
-- --                                 (resp r2)
-- --             helperComp = {!!}
-- --             -- toPathP (sym (transportComposite (compPath (eq2 r1) (eq1 r1)) (λ i → X (inextD D b (toApproxExactCommandD D ix b com i) (p i))) (lx r1))
-- --             --   ∙ congPath (λ pf → transportPath pf (lx r1)) eqPf ∙ fromPathP helperLx)
-- --             --     where
-- --             --       eqPf : compPath (compPath (eq2 r1) (eq1 r1))
-- --             --                 (λ i → X (inextD D b (toApproxExactCommandD D ix b com i) (p i)))
-- --             --                 ≡c (λ i → X (inextD D b com (r12Path i)))
-- --             --       eqPf i j = {!!}
-- --       -- compEqPath (symPath (transportComposite  _ _ (resp (toApproxResponseD ⦃ æ = Exact ⦄ D cs com (substPath (ResponseD ⦃ æ = _ ⦄ D cs)
-- --       --                                                                                                                             (toApproxExactCommandD D i cs com) (toExactResponseD D cs com r1))) )))
-- --       --                           {!!}))
-- -- -- Goal: PathP
-- -- --       (λ i₁ →
-- -- --          X (inextD D cs (toApproxExactCommandD D i cs com i₁) (p i₁)))
-- -- --       (transportPath
-- -- --        (compPath
-- -- --         (cong₂ (λ x y → X (inextD D cs x (toApproxResponseD D cs x y)))
-- -- --          (symPath (toApproxExactCommandD D i cs com))
-- -- --          (symP
-- -- --           (transport-filler
-- -- --            (congPath (ResponseD D cs) (toApproxExactCommandD D i cs com))
-- -- --            (toExactResponseD D cs com r1))))
-- -- --         (λ i₁ →
-- -- --            X (inextD D cs com (toApproxExactResponseD D cs com r1 i₁))))
-- -- --        (resp
-- -- --         (toApproxResponseD D cs com
-- -- --          (substPath (ResponseD D cs) (toApproxExactCommandD D i cs com)
-- -- --           (toExactResponseD D cs com r1)))))
-- -- --       (resp r2)


--     toApproxμ tyCtor cI cB Ds iStart b W⁇ = W⁇
--     toApproxμ tyCtor cI cB Ds iStart b W℧ = W℧
--     toApproxμ tyCtor cI cB Ds iStart b (Wsup (FC (d , com) resp)) = Wsup (FC (d , ⟦_⟧F.command recVal) (⟦_⟧F.response recVal))
--       module Aμ where
--         recVal =
--           toApproxDesc
--           {X = λ j → W̃ (Arg (λ d → interpDesc {{æ = Exact}} (Ds d) b)) j}
--           {Y = λ j → W̃ (Arg (λ d → interpDesc {{æ = Approx}} (Ds d) b)) j}
--           (Ds d)
--           b
--           _
--           (FC com resp)
--           λ r → toApproxμ tyCtor cI cB (λ d₁ → Ds d₁) _ b (resp r)
--     toExactμ tyCtor cI cB Ds iStart b W⁇ = W⁇
--     toExactμ tyCtor cI cB Ds iStart b W℧ = W℧
--     toExactμ tyCtor cI cB Ds iStart b (Wsup (FC (d , com) resp)) = Wsup (FC (d , ⟦_⟧F.command recVal) (⟦_⟧F.response recVal))
--       module Eμ where
--         recVal =
--           toExactDesc
--           {X = λ j → W̃ (Arg (λ d → interpDesc {{æ = Approx}} (Ds d) b)) j}
--           {Y = λ j → W̃ (Arg (λ d → interpDesc {{æ = Exact}} (Ds d) b)) j}
--           (Ds d)
--           b
--           _
--           (FC com resp)
--           λ r → toExactμ tyCtor cI cB (λ d₁ → Ds d₁) _ b (resp r)

--     toApproxExactμ tyCtor cI cB Ds iStart b W⁇ = refl
--     toApproxExactμ tyCtor cI cB Ds iStart b W℧ = refl
--     toApproxExactμ tyCtor cI cB Ds iStart b (Wsup (FC (d , com) resp))
--       = cong₂
--         {A = typeof com}
--         {B = λ c → (r : ResponseD {{æ = _}} (Ds d) b c) → W̃ (Arg (λ d → interpDesc {{æ = Approx}} (Ds d) b)) (inextD (Ds d) b c r) }
--         (λ c r → Wsup (FC (d , c) r))
--         (toApproxExactCommandD _ _ _ com)
--         (funExtDep λ {r1} {r2} pf → (helper r1 r2 pf))
--       where
--         Y = W̃ (Arg (λ d → interpDesc {{æ = Approx}} (Ds d) b))
--         comcom = (toApproxCommandD {{æ = Exact}} (Ds d) iStart b (toExactCommandD (Ds d) iStart b com))
--         helper :
--           (r1 : ResponseD {{æ = _}} (Ds d) b comcom)
--           → (r2 : ResponseD {{æ = _}} (Ds d) b com)
--           → (pth : PathP (λ i → ResponseD {{æ = _}} (Ds d) b (toApproxExactCommandD (Ds d) iStart b com i)) r1 r2)
--           → PathP (λ i → Y (inextD (Ds d) b (toApproxExactCommandD (Ds d) iStart b com i) (pth i)))
--             (transport (cong₂ (λ c r → Y (inextD (Ds d) b c r)) refl (toApproxExactResponseD (Ds d) b comcom r1))
--             (toApproxμ tyCtor cI cB Ds (inextD (Ds d) b comcom (toApproxResponseD {{æ = Exact}} (Ds d) b comcom
--                                                                  (toExactResponseD (Ds d) b comcom r1))) b
--             (transportPath
--               (cong₂ (λ c r → W̃ _ (inextD (Ds d) b c (toApproxResponseD {{æ = Exact}} (Ds d) b c r))) (symPath (toApproxExactCommandD (Ds d) _ b com)) (symP (toPathP refl)))
--               (toExactμ tyCtor cI cB Ds
--                 (inextD (Ds d) b com
--                   (toApproxResponseD {{æ = Exact}} (Ds d) b com
--                    (transportPath
--                     (λ i →
--                        ResponseD {{æ = _}} (Ds d) b
--                        (symPath (toApproxExactCommandD (Ds d) iStart b com) (~ i)))
--                     (toExactResponseD (Ds d) b comcom r1))))
--                 b
--                 (resp
--                  (toApproxResponseD {{æ = Exact}} (Ds d) b com
--                   (transportPath
--                    (λ i →
--                       ResponseD {{æ = _}} (Ds d) b (toApproxExactCommandD (Ds d) iStart b com i))
--                    (toExactResponseD (Ds d) b
--                     (toApproxCommandD {{æ = Exact}} (Ds d) iStart b
--                      (⟦_⟧F.command (Eμ.recVal tyCtor cI cB Ds iStart b d com resp)))
--                     r1))))))))
--             (resp r2)
--         helper = {!toApproxμ tyCtor cI cB Ds!}
--       -- cong₂ (λ x y → Wsup (FC (d , x) y)) (toApproxExactCommandD ((Ds d)) iStart b com)
--       --   (funExtDep (λ {r1} {r2} pf → compPathEq {!!} (toApproxExactμ tyCtor cI cB Ds _ b (resp r2))))
--     --   cong₂
--     --     FC
--     --       (toApproxExactCommandD D i cs com)
--     --       (funExtDep λ {r1} {r2} p → symP (toPathP (congPath (transportPath _) (symPath (toApproxExactμ ? ? ? ? ? ? ? )))))
--     --     where open import Cubical.Functions.FunExtEquiv using (funExtDep)
-- -- -- -----------------------------------------------------------------------




-- -- -- -- -- We can then recursively build the codes for each level
-- -- -- -- -- We take a guarded fixed-point, so we can have a code CSelf such that
-- -- -- -- -- El CSelf = ℂ
-- -- -- -- -- This gives us a version of Girard's Paradox that is safely stowed behind the guarded modality
-- -- -- -- CodeModuleAt : ∀  ℓ →  CodeModule ℓ
-- -- -- -- CodeModuleAt zero = --G.fix λ ModSelf →
-- -- -- --   record
-- -- -- --     { ℂ-1 = 𝟘
-- -- -- --     ; El-1 = λ ()
-- -- -- --     -- ; ⁇-1 = 𝟘
-- -- -- --     -- ; ℧-1 = λ { {{()}} }
-- -- -- --     -- ; ℂSelf = map▹ CodeModule.ℂ ModSelf
-- -- -- --     }
-- -- -- -- CodeModuleAt (suc ℓ) = -- G.fix λ ModSelf →
-- -- -- --   record
-- -- -- --     { ℂ-1 = CodeModule.ℂ (CodeModuleAt ℓ)
-- -- -- --     ; El-1 = λ x → CodeModule.El (CodeModuleAt ℓ) x
-- -- -- --     -- ; ⁇-1 = CodeModule.⁇ (CodeModuleAt ℓ)
-- -- -- --     -- ; ℧-1 = CodeModule.ℂ.C℧
-- -- -- --     -- ; ℂSelf = map▹ CodeModule.ℂ ModSelf
-- -- -- --     }


-- -- -- -- -- If we have smaller codes, ℓ > 0
-- -- -- -- ℓsuc : ∀ {ℓ} → CodeModule.ℂ-1 (CodeModuleAt ℓ) → Σ[ ℓ' ∈ ℕ ](ℓ ≡p suc ℓ')
-- -- -- -- ℓsuc {suc ℓ} x = _ , reflp

-- -- -- -- -- Expose each value in the Code module with implicit level ℓ
-- -- -- -- -- Except for ℂ and ⁇, which each need an explicit level
-- -- -- -- module CIMod {ℓ} where
-- -- -- --   open CodeModule (CodeModuleAt ℓ) public hiding (ℂ ; ⁇ )

-- -- -- -- open CIMod public

-- -- -- -- -- Make the levels explicit for each code
-- -- -- -- ℂ : ℕ → Set
-- -- -- -- ℂ ℓ = CodeModule.ℂ (CodeModuleAt ℓ)

-- -- -- -- -- ⁇Ty : ∀ {{_ : Æ}} ℓ → Set
-- -- -- -- -- ⁇Ty {{æ}} ℓ = (CodeModule.⁇ (CodeModuleAt ℓ) {{æ}})


-- -- -- -- -- ⁇lob : ∀ {{ _ : Æ }} {ℓ} → ⁇Ty ℓ ≡ F⁇ {ℓ} (A.next (⁇Ty ℓ))
-- -- -- -- -- ⁇lob {ℓ} = cong (λ P → F⁇ {ℓ} P) (A.pfix (F⁇ {ℓ}))



-- -- -- -- -- unfold⁇ : ∀ {{_ : Æ}} {ℓ} → ⁇Ty ℓ →  F⁇ (A.next (⁇Ty ℓ))
-- -- -- -- -- unfold⁇ {ℓ} x = subst (λ x → x) ⁇lob x


-- -- -- -- -- fold⁇ : ∀ {{_ : Æ}} {ℓ} →  F⁇ (A.next (⁇Ty ℓ))  → ⁇Ty ℓ
-- -- -- -- -- fold⁇ {ℓ} x = subst (λ x → x) (sym ⁇lob) x


-- -- -- -- -- ℂ-1>0 : ∀ {ℓ} → ℂ-1 {ℓ = ℓ} → 0< ℓ
-- -- -- -- -- ℂ-1>0 {suc ℓ} x = suc<

-- -- -- -- -- -- The least precise argument to a guarded function from ⁇ to ⁇
-- -- -- -- -- -- Used for checking if functions are errors
-- -- -- -- -- -- topArg : ∀ {ℓ} → ▸ map▹ ⁇Self (dfix (λ args → selfRec (F⁇ {ℓ} args) ⁇℧))
-- -- -- -- -- -- topArg {ℓ} = Dep▸ ℧Self (dfix (λ args → selfRec (F⁇ {ℓ} args) ⁇℧))



-- -- -- -- -- -- Relation for whether a value is an error in type ⁇
-- -- -- -- -- -- data ℧≡ {ℓ} : ⁇Ty ℓ → Set where
-- -- -- -- -- --          ℧℧ : ℧≡ ⁇℧
-- -- -- -- -- --          ⁇Π℧ : ∀ {f} → ⁇℧ ≡ f topArg  → ℧≡ (⁇Π f)
-- -- -- -- -- --          -- ⁇Π℧ : ∀ {f : ▸ map▹ ⁇Self Self → F⁇ Self  } → ⁇℧ ≡ f (λ tic → ℧Self (Self tic))  → ℧≡ (⁇Π f)
-- -- -- -- -- --          ⁇Type℧ : {{_ : 0< ℓ}} → ℧≡ (⁇Type ℧-1)
-- -- -- -- -- --          ⁇Σ℧ : ℧≡ (⁇Σ (⁇℧ , ⁇℧))
-- -- -- -- -- --          ⁇≡℧ : ℧≡ (⁇≡ ⁇℧)
-- -- -- -- -- --          ⁇μ℧ : ∀ (tyCtor : CName) (ctor : DName tyCtor)
-- -- -- -- -- --            → ℧≡ (⁇μ tyCtor ctor μ℧)


-- -- -- -- -- -- -- Every type has an error element
-- -- -- -- -- -- ℧ : ∀ {{æ : Æ}} {ℓ} → (c : ℂ ℓ)  → El c
-- -- -- -- -- -- ℧ CodeModule.C⁇ = ⁇℧
-- -- -- -- -- -- ℧ CodeModule.C℧ = tt
-- -- -- -- -- -- ℧ CodeModule.C𝟘 = tt
-- -- -- -- -- -- ℧ CodeModule.C𝟙 = false
-- -- -- -- -- -- ℧ {suc ℓ} CodeModule.CType = C℧
-- -- -- -- -- -- ℧ (CodeModule.CΠ dom cod) = λ x → (℧ (cod (approx x)))
-- -- -- -- -- -- ℧ (CodeModule.CΣ dom cod)  = ℧ dom , ℧ (cod (CodeModule.approx (CodeModuleAt _) (℧ dom)))
-- -- -- -- -- -- --withApprox (λ æ₁ → ℧ ⦃ æ₁ ⦄ dom) , ℧ (cod _)
-- -- -- -- -- -- -- ℧ (CodeModule.CΣ dom cod) ⦃ Exact ⦄ = (℧ dom {{Approx}} , ℧ dom {{Exact}}) , ℧ (cod (℧ dom {{Approx}})) {{Exact}}
-- -- -- -- -- -- ℧ (CodeModule.C≡ c x y) = ℧ {{Approx}} c ⊢ x ≅ y
-- -- -- -- -- -- ℧ (CodeModule.Cμ tyCtor c D x) = W℧
-- -- -- -- -- -- ℧ {ℓ = suc ℓ} (CCumul c) = ℧ c

-- -- -- -- -- -- ℧Approx : ∀ {ℓ} (c : ℂ ℓ) → ApproxEl c
-- -- -- -- -- -- ℧Approx = ℧ {{Approx}}

-- -- -- -- -- -- -- ℧Approxed : ∀ {{æ : Æ}} {ℓ} (c : ℂ ℓ) → El c
-- -- -- -- -- -- -- ℧Approxed c = withApprox λ æ → ℧ {{æ = æ}} c


-- -- -- -- -- -- DCtors : ∀ {ℓ} → CName → ℂ ℓ → Set
-- -- -- -- -- -- DCtors tyCtor cI = (d : DName tyCtor) → ℂDesc cI C𝟘 (indSkeleton tyCtor d)

-- -- -- -- -- -- ▹⁇ : {{_ : Æ}} →  ℕ → A.▹ Set
-- -- -- -- -- -- ▹⁇ ℓ = A.dfix (F⁇ {ℓ})

-- -- -- -- -- -- ▹⁇≡ : ∀ {{_ : Æ}} {ℓ} → ▹⁇ ℓ ≡ A.next (⁇Ty ℓ)
-- -- -- -- -- -- ▹⁇≡ = A.pfix F⁇

-- -- -- -- -- -- apply▸ : ∀ {{_ : Æ}} {ℓ} (f : (A.▸ (A.dfix (F⁇ {ℓ = ℓ}))) → ⁇Ty ℓ) → (x : A.▹ (⁇Ty ℓ)) →  ⁇Ty ℓ
-- -- -- -- -- -- apply▸ f x = f (transport (cong A.▹_ (⁇lob ∙ cong F⁇ (sym ▹⁇≡)) ∙ sym A.hollowEq ) x)

-- -- -- -- -- -- WUnk : ∀ {{æ : Æ}} → ℕ → Set
-- -- -- -- -- -- WUnk ℓ = (FWUnk {ℓ = ℓ} (▹⁇ ℓ))

-- -- -- -- -- -- ⁇ToW : ∀ {{æ : Æ}} {ℓ} → ⁇Ty ℓ → WUnk ℓ
-- -- -- -- -- -- ⁇ToW ⁇⁇ = W⁇
-- -- -- -- -- -- ⁇ToW ⁇℧ = W℧
-- -- -- -- -- -- ⁇ToW ⁇𝟙 = Wsup (FC ( H𝟙 , tt) λ ())
-- -- -- -- -- -- ⁇ToW {ℓ = suc ℓ} (⁇Type ty) = Wsup (FC ( HType , ty) λ ())
-- -- -- -- -- -- ⁇ToW {ℓ = suc ℓ} (⁇Cumul c x) = Wsup (FC ( HCumul , (c , x)) λ ())
-- -- -- -- -- -- ⁇ToW (⁇Π f) = Wsup (FC ( HΠ , tt) λ x → ⁇ToW (f x))
-- -- -- -- -- -- ⁇ToW (⁇Σ (x , y)) = Wsup (FC ( HΣ , tt) λ r → if r then ⁇ToW x else ⁇ToW y)
-- -- -- -- -- -- ⁇ToW (⁇≡ (x ⊢ _ ≅ _)) = Wsup (FC ( H≅ , tt) λ _ → ⁇ToW x)
-- -- -- -- -- -- ⁇ToW (⁇μ tyCtor x) = Wsup (FC ( (HCtor tyCtor) , tt) λ _ → x)


-- -- -- -- -- -- ⁇FromW : ∀ {{æ : Æ}} {ℓ} → WUnk ℓ → ⁇Ty ℓ
-- -- -- -- -- -- ⁇FromW (Wsup (FC (HΠ , arg) res)) = ⁇Π (λ x → ⁇FromW (res x))
-- -- -- -- -- -- ⁇FromW (Wsup (FC (HΣ , arg) res)) = ⁇Σ ((⁇FromW (res true)) , (⁇FromW (res false)))
-- -- -- -- -- -- ⁇FromW (Wsup (FC (H≅ , arg) res)) = ⁇≡ ((⁇FromW (res tt)) ⊢ _ ≅ _)
-- -- -- -- -- -- ⁇FromW (Wsup (FC (H𝟙 , arg) res)) = ⁇𝟙
-- -- -- -- -- -- ⁇FromW {ℓ = suc ℓ} (Wsup (FC (HType , c) res)) = ⁇Type {{inst = suc<}} c
-- -- -- -- -- -- ⁇FromW {ℓ = suc ℓ} (Wsup (FC (HCumul , (c , x)) res)) = ⁇Cumul {{inst = suc<}} c x
-- -- -- -- -- -- ⁇FromW (Wsup (FC (HCtor tyCtor , arg) res)) = ⁇μ tyCtor (res tt)
-- -- -- -- -- -- ⁇FromW W⁇ = ⁇⁇
-- -- -- -- -- -- ⁇FromW W℧ = ⁇℧

-- -- -- -- -- -- ⁇IsoWL : ∀ {{æ : Æ}} {ℓ} → (x : ⁇Ty ℓ) → ⁇FromW (⁇ToW x) ≡ x
-- -- -- -- -- -- ⁇IsoWL ⁇⁇ = reflc
-- -- -- -- -- -- ⁇IsoWL ⁇℧ = reflc
-- -- -- -- -- -- ⁇IsoWL ⁇𝟙 = reflc
-- -- -- -- -- -- ⁇IsoWL {ℓ = suc ℓ} (⁇Type ⦃ inst = suc< {ℓ = .ℓ} ⦄ x) = reflc
-- -- -- -- -- -- ⁇IsoWL {ℓ = suc ℓ} (⁇Cumul ⦃ inst = suc< {ℓ = .ℓ} ⦄ c x) = reflc
-- -- -- -- -- -- ⁇IsoWL (⁇Π f) = cong ⁇Π (funExt λ x → ⁇IsoWL (f x))
-- -- -- -- -- -- ⁇IsoWL (⁇Σ (x , y)) = cong₂ (λ x y → ⁇Σ (x , y)) (⁇IsoWL x) (⁇IsoWL y)
-- -- -- -- -- -- ⁇IsoWL (CodeModule.⁇≡ (x ⊢ .⁇⁇ ≅ .⁇⁇)) = cong (λ x → ⁇≡ (x ⊢ _ ≅ _)) (⁇IsoWL x)
-- -- -- -- -- -- ⁇IsoWL (⁇μ tyCtor x) = reflc

-- -- -- -- -- -- Wsup-cong : ∀ {I} {C : Container I} {i : I} → {com : Command C i} → {x y : (res : Response C com) → W̃ C (inext C com res)} → x ≡ y → Wsup (FC com x) ≡c Wsup (FC com y)
-- -- -- -- -- -- Wsup-cong {com = com} {x = x} {y = y} pf = cong {x = x} {y = y} (λ x → Wsup (FC _ x)) pf

-- -- -- -- -- -- ⁇IsoWR : ∀ {{æ : Æ}} {ℓ} (x : WUnk ℓ)  → ⁇ToW (⁇FromW x) ≡ x
-- -- -- -- -- -- ⁇IsoWR (Wsup (FC (HΠ , tt) f)) = Wsup-cong (funExt λ x → ⁇IsoWR (f x))
-- -- -- -- -- -- ⁇IsoWR (Wsup (FC (HΣ , tt) res)) = Wsup-cong (funExt (λ {true → ⁇IsoWR (res true) ; false → ⁇IsoWR (res false)}))
-- -- -- -- -- -- ⁇IsoWR (Wsup (FC (H≅ , arg) res)) = Wsup-cong (funExt (λ (tt) → ⁇IsoWR (res tt)))
-- -- -- -- -- -- ⁇IsoWR (Wsup (FC (H𝟙 , arg) res)) = Wsup-cong (funExt (λ ()))
-- -- -- -- -- -- ⁇IsoWR {ℓ = suc ℓ} (Wsup (FC (HType , arg) res)) = Wsup-cong (funExt λ ())
-- -- -- -- -- -- ⁇IsoWR {ℓ = suc ℓ} (Wsup (FC (HCumul , arg) res)) = Wsup-cong (funExt λ ())
-- -- -- -- -- -- ⁇IsoWR (Wsup (FC (HCtor x , arg) res)) = Wsup-cong (funExt (λ x → reflc))
-- -- -- -- -- -- ⁇IsoWR W℧ = reflc
-- -- -- -- -- -- ⁇IsoWR W⁇ = reflc


-- -- -- -- -- -- ⁇DescIso : ∀ {{_ : Æ}} {ℓ} → Iso (⁇Ty ℓ) (WUnk ℓ)
-- -- -- -- -- -- ⁇DescIso = iso ⁇ToW ⁇FromW ⁇IsoWR ⁇IsoWL

-- -- -- -- -- -- -- -- ⁇ : ∀ {ℓ} → (c : ℂ ℓ) → {{æ : Æ}} → El c
-- -- -- -- -- -- -- -- ⁇ CodeModule.C⁇ = ⁇⁇
-- -- -- -- -- -- -- -- ⁇ CodeModule.C℧ = tt
-- -- -- -- -- -- -- -- ⁇ CodeModule.C𝟘 = tt
-- -- -- -- -- -- -- -- ⁇ CodeModule.C𝟙 = false
-- -- -- -- -- -- -- -- ⁇ {suc ℓ} CodeModule.CType = C⁇
-- -- -- -- -- -- -- -- ⁇ (CodeModule.CΠ dom cod) = λ x → (⁇ (cod (approx x)))
-- -- -- -- -- -- -- -- ⁇ (CodeModule.CΣ dom cod)  = pairWithApprox (⁇ dom {{Approx}}) (⁇ dom ) , ⁇ (cod _)
-- -- -- -- -- -- -- -- -- ⁇ (CodeModule.CΣ dom cod) ⦃ Exact ⦄ = (⁇ dom {{Approx}} , ⁇ dom {{Exact}}) , ⁇ (cod (⁇ dom {{Approx}})) {{Exact}}
-- -- -- -- -- -- -- -- ⁇ (CodeModule.C≡ c x y) = ⁇⊢ x ≅ y
-- -- -- -- -- -- -- -- ⁇ (CodeModule.Cμ tyCtor c D x) = W⁇

-- -- -- -- -- -- -- -- {-# DISPLAY CodeModule.ℂ _ = ℂ  #-}
-- -- -- -- -- -- -- -- {-# DISPLAY CodeModule.El _  = El  #-}



-- -- -- -- -- -- -- -- -- -- Lift a code to a higher universe
-- -- -- -- -- -- -- -- -- liftℂ : ∀ {j k} → j ≤ k → ℂ j → ℂ k
-- -- -- -- -- -- -- -- -- liftDesc : ∀ {j k} → (pf : j ≤ k) → (c : ℂ j) → ℂDesc {j} c → ℂDesc {k} (liftℂ pf c)
-- -- -- -- -- -- -- -- -- toLift : ∀ {j k} (pf : j ≤ k) (c : ℂ j) → El c →  El (liftℂ pf c)
-- -- -- -- -- -- -- -- -- fromLift : ∀ {j k} (pf : j ≤ k) (c : ℂ j) →  El (liftℂ pf c) → El c
-- -- -- -- -- -- -- -- -- fromToLift : ∀ {j k} (pf : j ≤ k) (c : ℂ j) (x : El c) → fromLift pf c (toLift pf c x ) ≡ x
-- -- -- -- -- -- -- -- -- liftℂ pf CodeModule.C⁇ = C⁇
-- -- -- -- -- -- -- -- -- liftℂ pf CodeModule.C℧ = C℧
-- -- -- -- -- -- -- -- -- liftℂ pf CodeModule.C𝟘 = C𝟘
-- -- -- -- -- -- -- -- -- liftℂ pf CodeModule.C𝟙 = C𝟙
-- -- -- -- -- -- -- -- -- liftℂ (zero , pf) CodeModule.CType = transport (cong ℂ pf) CType
-- -- -- -- -- -- -- -- -- liftℂ (suc diff , pf) CodeModule.CType = CType {{transport (cong 0< pf) suc<}}
-- -- -- -- -- -- -- -- -- liftℂ pf (CodeModule.CΠ dom cod) = CΠ (liftℂ pf dom) (λ x → (liftℂ pf (cod (fromLift pf dom x))))
-- -- -- -- -- -- -- -- -- liftℂ pf (CodeModule.CΣ dom cod) = CΣ (liftℂ pf dom) (λ x → (liftℂ pf (cod (fromLift pf dom x))))
-- -- -- -- -- -- -- -- -- liftℂ pf (CodeModule.C≡ c x y) = C≡ (liftℂ pf c) (toLift pf c x) (toLift pf c y)
-- -- -- -- -- -- -- -- -- liftℂ pf (CodeModule.Cμ tyCtor c D x) = Cμ tyCtor (liftℂ pf c) (λ ctor → liftDesc pf c (D ctor)) (toLift pf c x)

-- -- -- -- -- -- -- -- -- liftDesc pf c (CodeModule.CEnd i) = CEnd (toLift pf c i)
-- -- -- -- -- -- -- -- -- liftDesc pf c (CodeModule.CArg c₁ D) = CArg (liftℂ pf c₁) (λ x → liftDesc pf c (D (fromLift pf c₁ x)))
-- -- -- -- -- -- -- -- -- liftDesc pf c (CodeModule.CRec c₁ j D) =
-- -- -- -- -- -- -- -- --   CRec (liftℂ pf c₁) (λ x → toLift pf c (j (fromLift pf c₁ x))) λ x → liftDesc pf c (D (fromLift pf c₁ x))

-- -- -- -- -- -- -- -- -- toLift pf CodeModule.C℧ x = tt
-- -- -- -- -- -- -- -- -- toLift pf CodeModule.C𝟘 x = x
-- -- -- -- -- -- -- -- -- toLift pf CodeModule.C𝟙 x = x
-- -- -- -- -- -- -- -- -- toLift {j = suc j} {zero} (_ , pf) CodeModule.CType x with () ← snotz (sym (+-suc _ j) ∙ pf)
-- -- -- -- -- -- -- -- -- toLift {j = suc j} {suc k} (diff , pf) CodeModule.CType x = liftℂ (zero , injSuc pf) x
-- -- -- -- -- -- -- -- -- toLift {j = suc j} {suc k} (suc diff , pf) CodeModule.CType x = liftℂ (suc diff , sym (+-suc _ j) ∙ injSuc pf) x
-- -- -- -- -- -- -- -- -- toLift pf (CodeModule.CΠ dom cod) f = λ x → toLift pf (cod (fromLift pf dom x)) (f (fromLift pf dom x))
-- -- -- -- -- -- -- -- -- toLift pf (CodeModule.CΣ dom cod) (x , y) =
-- -- -- -- -- -- -- -- --   toLift pf dom x , transport (cong (λ x → El (liftℂ pf (cod x))) (sym (fromToLift pf dom x))) (toLift pf (cod x) y)
-- -- -- -- -- -- -- -- -- toLift pf (CodeModule.C≡ c x₁ y) x = toLift pf c x
-- -- -- -- -- -- -- -- -- toLift pf (CodeModule.Cμ tyCtor c D x₁) x = {!!}
-- -- -- -- -- -- -- -- -- toLift pf CodeModule.C⁇ x = {!!}

-- -- -- -- -- -- -- -- -- fromLift pf CodeModule.C℧ x = tt
-- -- -- -- -- -- -- -- -- fromLift pf CodeModule.C𝟘 x = tt
-- -- -- -- -- -- -- -- -- fromLift pf CodeModule.C𝟙 x = x
-- -- -- -- -- -- -- -- -- fromLift (zero , pf) CodeModule.CType x = transport (sym (cong (λ x → CodeModule.ℂ-1 (CodeModuleAt x)) pf)) x
-- -- -- -- -- -- -- -- -- -- This is the only place we differ: can't lower the level of a type
-- -- -- -- -- -- -- -- -- fromLift {suc j} (suc diff , pf) CodeModule.CType x = C℧
-- -- -- -- -- -- -- -- -- fromLift pf (CodeModule.CΠ dom cod) f = λ x →
-- -- -- -- -- -- -- -- --   fromLift pf (cod x) (transport (cong (λ x → El (liftℂ pf (cod x))) (fromToLift pf dom x)) (f (toLift pf dom x)) )
-- -- -- -- -- -- -- -- -- fromLift pf (CodeModule.CΣ dom cod) (x , y) = fromLift pf dom x , fromLift pf (cod (fromLift pf dom x)) y
-- -- -- -- -- -- -- -- -- fromLift pf (CodeModule.C≡ c x₁ y) x = fromLift pf c x
-- -- -- -- -- -- -- -- -- fromLift pf (CodeModule.Cμ tyCtor c D x₁) x = {!!}
-- -- -- -- -- -- -- -- -- fromLift pf CodeModule.C⁇ x = {!!}

-- -- -- -- -- -- -- -- -- fromToLift pf CodeModule.C℧ x = refl
-- -- -- -- -- -- -- -- -- fromToLift pf CodeModule.C𝟘 x = refl
-- -- -- -- -- -- -- -- -- fromToLift pf CodeModule.C𝟙 x = refl
-- -- -- -- -- -- -- -- -- fromToLift {j = suc j} {zero} (_ , pf) CodeModule.CType x = {!!}
-- -- -- -- -- -- -- -- -- fromToLift {j = suc j} {suc k} (zero , pf) CodeModule.CType x = {!!}
-- -- -- -- -- -- -- -- -- fromToLift {j = suc j} {suc k} (suc diff , pf) CodeModule.CType x = {!!}
-- -- -- -- -- -- -- -- -- fromToLift pf (CodeModule.CΠ c cod) x = {!!}
-- -- -- -- -- -- -- -- -- fromToLift pf (CodeModule.CΣ c cod) x = {!!}
-- -- -- -- -- -- -- -- -- fromToLift pf (CodeModule.C≡ c x₁ y) x = {!!}
-- -- -- -- -- -- -- -- -- fromToLift pf (CodeModule.Cμ tyCtor c D x₁) x = {!!}
-- -- -- -- -- -- -- -- -- fromToLift pf CodeModule.C⁇ x = {!!}
