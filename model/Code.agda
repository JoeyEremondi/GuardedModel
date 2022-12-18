{-# OPTIONS --cubical --guarded #-}
-- open import Desc
-- open import Level hiding (#_)
open import Cubical.Data.Nat renaming (Unit to 𝟙)
open import Cubical.Data.Fin hiding (_/_)
-- open import Cubical.Data.Bool renaming (Bool to 𝟚)
open import Cubical.Data.Empty renaming (⊥ to 𝟘)
open import Cubical.Data.Nat.Order
open import Cubical.HITs.SetQuotients
open import DecPEq
open import Cubical.Data.Sigma

open import Cubical.Data.Bool
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
  constructor codeModule
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
  toApproxExact⁇ (⁇Cumul c x) = cong (λ x → ⁇Cumul {{æ = Approx}} c x) (toApproxExact-1 sc _ _)
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
    approxExact≡ : {{æ : Æ}} → {c : ℂ} → (x : ApproxEl c) → approx (exact x) ≡c x
    approxExact≡ {{æ = Approx}} x = reflc
    approxExact≡ {{æ = Exact}} x = toApproxExact _ x

    -- ApproxedEl : {{æ : Æ}} → ℂ → Set
    -- ApproxedEl {{æ}} c = Approxed (ÆEl c)

    -- Interpretation of codes when they're on the left of an arrow,
    -- used to make the germs of datatypes
    -- ▹El : ℂ → Set
    -- Code-based Descriptions of inductive data types
    data ℂDesc : ℂ → IndSig → Set
    -- Interpretation of description codes into W-types
    CommandD : ∀ {{æ : Æ}}  {cB sig} → ℂDesc cB sig → (ApproxEl cB → Set)
    ResponseD : ∀ {{æ :  Æ}} {cB sig} → (D : ℂDesc cB sig) → (b : ApproxEl cB) → CommandD {{æ = Approx}} D b → Set
    FWUnk : {{_ : Æ}} → A.▹ ⁇Self → Set
    -- ▹interpDesc : ∀{{ _ : Æ }} {I} → (ℂDesc I ) → Container 𝟙
    -- ▹CommandD : ∀ {{ _ : Æ }}{I} →  ℂDesc I  → Set
    -- ▹ResponseD : ∀ {{ _ : Æ }}{I} →  (D : ℂDesc I ) → ▹CommandD D → Set
    toApproxCommandD : ∀  {{æ : Æ}} {cB sig} → (D : ℂDesc cB sig) → (b : ApproxEl cB) → CommandD {{æ = æ}} D b → CommandD {{æ = Approx}} D b
    -- toApproxCommandDEq : ∀   {I cB sig} → (D : ℂDesc I cB sig) → (i : ApproxEl I) → (b : ApproxEl cB) → (x : CommandD {{æ = Approx}} D i b) → toApproxCommandD {{æ = Approx}} D i b x ≡c x
    toApproxResponseD : ∀ {{æ :  Æ}} {cB sig} → (D : ℂDesc cB sig) → (b : ApproxEl cB) → (com : CommandD {{æ = Approx}} D b)
      → ResponseD {{æ = æ}} D b com → ResponseD {{æ = Approx}} D b com
    toExactCommandD : ∀   {cB sig} → (D : ℂDesc cB sig) →  (b : ApproxEl cB) → CommandD {{æ = Approx}} D b → CommandD {{æ = Exact}} D b
    toExactResponseD : ∀  {cB sig} → (D : ℂDesc cB sig) →  (b : ApproxEl cB) → (com : CommandD {{æ = Approx}} D b)
      → ResponseD {{æ = Approx}} D b com → ResponseD {{æ = Exact}} D b com
    toApproxExactCommandD : ∀   {cB sig} → (D : ℂDesc cB sig) → (b : ApproxEl cB) → (c : CommandD {{æ = Approx}} D b)
      → toApproxCommandD {{æ = Exact}} D b (toExactCommandD D b c) ≡c c
    toApproxExactResponseD : ∀  {cB sig} → (D : ℂDesc cB sig) → (b : ApproxEl cB) → (com : CommandD {{æ = Approx}} D b)
      → (r : ResponseD {{æ = Approx}} D b com)
      → (toApproxResponseD {{æ = Exact}} D b com (toExactResponseD D b com r) ) ≡c r



    interpDesc : ∀ {{æ : Æ}} {cB} {sig} →  (ℂDesc cB sig) → ApproxEl cB → Container 𝟙
    --adapted from https://stackoverflow.com/questions/34334773/why-do-we-need-containers
    interpDesc {{æ = æ}} {cB = cB} D b  = (λ i → CommandD {{æ = æ}} D b) ◃ (λ c → ResponseD {{æ = æ}} D b (toApproxCommandD D b c)) / λ _ _ → tt

    toApproxDesc : ∀ { cB sig X Y}
          → (D : ℂDesc cB sig)
          → (b : ApproxEl cB)
          → (cs : ⟦ interpDesc {{æ = Exact}} D b ⟧F X tt)
          → □ (interpDesc {{æ = Exact}} D b) (λ (j , _) → Y j) (tt , cs)
          → ⟦ interpDesc {{æ = Approx}} D b ⟧F Y tt
    toExactDesc :
      ∀ { cB sig X Y}
          → (D : ℂDesc cB sig)
          → (b : ApproxEl cB)
          → (cs : ⟦ interpDesc {{æ = Approx}} D b ⟧F X tt)
          → □ (interpDesc {{æ = Approx}} D b) (λ (j , _) → Y j) (tt , cs)
          → ⟦ interpDesc {{æ = Exact}} D b ⟧F Y tt

    toApproxμ :
      (tyCtor : CName)
        → (cB : ℂ)
        → (D : (d : DName tyCtor) → ℂDesc cB (indSkeleton tyCtor d))
        → (b : ApproxEl cB)
        → W̃ (Arg (λ d → interpDesc {{æ = Exact}} (D d) b)) tt
        → W̃ (Arg (λ d → interpDesc {{æ = Approx}} (D d) b)) tt
    toExactμ :
      (tyCtor : CName)
        → (cB : ℂ)
        → (D : (d : DName tyCtor) → ℂDesc cB (indSkeleton tyCtor d))
        → (b : ApproxEl cB)
        → W̃ (Arg (λ d → interpDesc {{æ = Approx}} (D d) b)) tt
        → W̃ (Arg (λ d → interpDesc {{æ = Exact}} (D d) b)) tt
    toApproxExactμ :
        (tyCtor : CName)
          → (cB : ℂ)
          → (D : (d : DName tyCtor) → ℂDesc cB (indSkeleton tyCtor d))
          → (b : ApproxEl cB)
          → (x : W̃ (Arg (λ d → interpDesc {{æ = Approx}} (D d) b)) tt )
          → toApproxμ tyCtor cB D  b (toExactμ tyCtor cB D b x) ≡c x



    -- toApproxDesc : ∀  {I} {cB} {sig} →  (D : ℂDesc cB sig) → (b : ApproxEl cB) (i : ApproxEl I) → W̃  (interpDesc {{æ = Exact}} D b) i → W̃  (interpDesc {{æ = Approx}} D b) i
    -- toExactDesc : ∀  {I} {cB} {sig} →  (D : ℂDesc cB sig) → (b : ApproxEl cB) (i : ApproxEl I) → W̃  (interpDesc {{æ = Approx}} D b) i → W̃  (interpDesc {{æ = Exact}} D b) i
    -- toApproxExactDesc : ∀  {I} {cB} {sig} →  (D : ℂDesc cB sig) → (b : ApproxEl cB) (i : ApproxEl I) → (x : W̃  (interpDesc {{æ = Approx}} D b) i)
    --   → toApproxDesc D b i (toExactDesc D b i x) ≡ x
    -- toExactDesc : ∀  {I} {cB} {sig} →  (ℂDesc cB sig) → ApproxEl cB → Container (ApproxEl I)

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
    El C℧ = G𝟘
    toApprox C℧ _ = ℧𝟘
    toExact C℧ _ = ℧𝟘
    toApproxExact C℧ ℧𝟘 = refl
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
    El C𝟙 = G𝟙
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
    toApproxExact (CCumul c) x = toApproxExact-1 sc  c x
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
        → (D : (d : DName tyCtor) → ℂDesc C𝟙 (indSkeleton tyCtor d))
        → ApproxEl cI
        → ℂ
    El (Cμ tyCtor cI D i) = W̃ (Arg (λ d → interpDesc (D d) Gtt)) tt
    -- toApprox (Cμ tyCtor cI Ds iStart) (Wsup (FC (d , com) res)) =
    --   with (FC retCom retRes) ← toApproxDesc {Y = λ j → {!!}} (Ds d) true {!!} (FC com res) (λ r → {!!})
    --   = {!x!}
    -- toApprox (Cμ tyCtor cI Ds iStart) W⁇ = W⁇
    -- toApprox (Cμ tyCtor cI Ds iStart) W℧ = W℧
    toApprox (Cμ tyCtor cI Ds iStart) x = toApproxμ tyCtor C𝟙 Ds Gtt x
    toExact (Cμ tyCtor cI Ds iStart) x = toExactμ tyCtor C𝟙 Ds Gtt x
    toApproxExact (Cμ tyCtor cI Ds i) x = toApproxExactμ tyCtor C𝟙 Ds Gtt x

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
      CEnd : ∀ {cB} → ℂDesc cB SigE
      CArg : ∀ {cB} {rest} → (c : ApproxEl cB → ℂ) → (D : ℂDesc (CΣ cB c) rest) → (cB' : ℂ) → ((CΣ cB c) ≡p cB') → ℂDesc cB (SigA rest)
      CRec : ∀ {cB} {rest} (D :  ℂDesc cB rest) → ℂDesc cB (SigR rest)
      CHRec : ∀ {cB} {rest} → (c : ApproxEl cB → ℂ) → (D : ℂDesc cB rest)
        → (cB' : ℂ) → ((CΣ cB c) ≡p cB')
        → ℂDesc cB (SigHR rest)

    -- interpDesc D b  = CommandD D b  ◃ ResponseD  D  b  ◃  (λ _ → 𝟘) / inextD D b

    CommandD (CEnd) b = 𝟙
    CommandD (CArg c D _ _) b = Σ[ a ∈ El (c b) ] CommandD D (b , approx a)
    CommandD (CRec D) b = CommandD D b
    CommandD (CHRec c D _ _) b = CommandD D b
--     -- CommandD (CHGuard c D E) i =  ((▹ (El c)) → CommandD D i) × CommandD E i

    ResponseD (CEnd) b com = 𝟘
    ResponseD (CArg c D _ _) b (a , com) = ResponseD D (b , a) com
    ResponseD (CRec D) b com = Rec⇒ 𝟙    Rest⇒ (ResponseD D b com)
    ResponseD (CHRec c D _ _) b com = Rec⇒ (El (c b) )    Rest⇒ (ResponseD D b com)
    -- ResponseD (CHGuard c D E) (comD , comE) =
    --   GuardedArg⇒ (Σ[ a▹ ∈  ▹ El c ] (ResponseD D (comD a▹)))
    --     Rest⇒ ResponseD E comE



    -- inextD (CArg c D _ _) {i} b (a , com) res = inextD D (b ,  a) com res
    -- inextD (CRec D) {i} b com (Rec x) = ?
    -- inextD (CRec D) {i} b com (Rest x) = inextD D b com x
    -- inextD (CHRec c D _ _) {i} b com (Rec res) = j b (res)
    -- inextD (CHRec c D _ _) {i} b com (Rest res) = inextD D b com res
    -- -- inextD (CHGuard c D D₁) {i} (f , com) (GuardedArg (a , res)) = inextD D (f a) res
    -- -- inextD (CHGuard c D D₁) {i} (a , com) (GRest x) = inextD D₁ com x


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


    open import Cubical.HITs.PropositionalTruncation


    toApproxCommandD {{æ = Approx}} D b com = com
    toApproxCommandD (CEnd ) b com = com
    toApproxCommandD (CArg c D cB' x) b (a , com) = approx  {c = c b}  a , toApproxCommandD D (b , approx {c = c b} a) com
    toApproxCommandD (CRec D) b com = toApproxCommandD D b com
    toApproxCommandD (CHRec c D cB' x) b com = toApproxCommandD D b com

    toApproxResponseD {{æ = Approx}} D b com r = r
    toApproxResponseD (CArg c D cB' x) b com r = toApproxResponseD D (b , (fst com)) (snd com) r
    toApproxResponseD (CRec  D) b com (Rec x) = Rec tt
    toApproxResponseD (CRec  D) b com (Rest r) = Rest (toApproxResponseD D b _ r)
    toApproxResponseD (CHRec c  D cB' x) b com (Rec r) = Rec (approx {c = (c b)} r)
    toApproxResponseD (CHRec c  D cB' x) b com (Rest r) = Rest (toApproxResponseD D b _ r)

    toExactCommandD (CEnd ) b com = com
    toExactCommandD (CArg c D cB' x) b (a , com) = toExact (c b) a , toExactCommandD D (b , _) (substPath (λ a → CommandD ⦃ æ = Approx ⦄ D (b , a)) (symPath (toApproxExact (c b) a)) com)
    toExactCommandD (CRec  D) b com = toExactCommandD D b com
    toExactCommandD (CHRec c  D cB' x) b com = toExactCommandD D b com

    toExactResponseD (CArg c D cB' x) b com r = toExactResponseD D (b , (fst com)) (snd com) r
    toExactResponseD (CRec  D) b com (Rec x) = Rec tt
    toExactResponseD (CRec  D) b com (Rest r) = Rest (toExactResponseD D b _ r)
    toExactResponseD (CHRec c D cB' x) b com (Rec r) = Rec (toExact (c b) r)
    toExactResponseD (CHRec c D cB' x) b com (Rest r) = Rest (toExactResponseD D b _ r)

    toApproxExactCommandD (CEnd) b com = refl
    toApproxExactCommandD (CArg c D cB' x) b (a , com) =
      ΣPathP
        (toApproxExact (c b) a
        , compPathEq (congP (λ _ x → toApproxCommandD ⦃ æ = Exact ⦄ D _ (toExactCommandD D _ x )) pth) (toApproxExactCommandD D _ com))
      where
        pth = symP (subst-filler (λ v → CommandD {{æ = _}} D (b , v)) (λ i₁ → toApproxExact (c b) a (~ i₁)) com)
    toApproxExactCommandD (CRec D) b com = toApproxExactCommandD D b com
    toApproxExactCommandD (CHRec c D cB' x) b com = toApproxExactCommandD D b com

    toApproxExactResponseD (CArg c D cB' x) b com r = toApproxExactResponseD D _ (snd com) r
    toApproxExactResponseD (CRec D) b com (Rec tt) = refl
    toApproxExactResponseD (CRec D) b com (Rest r) = congPath Rest (toApproxExactResponseD D b com r)
    toApproxExactResponseD (CHRec c D cB' x) b com (Rec r) = congPath Rec (toApproxExact (c b) r)
    toApproxExactResponseD (CHRec c D cB' x) b com (Rest r) = congPath Rest (toApproxExactResponseD D b com r)


    -- transportIndexPathP :
    --   ∀ {{æ : Æ}} { cI cB } {tyCtor : CName}
    --     → (D : (d : DName tyCtor) → ℂDesc cB (indSkeleton tyCtor d))
    --     → (b : ApproxEl cB)
    --     → (i j : ApproxEl cI)
    --     → (i≡j : i ≡c j)
    --     → (x : W̃ (Arg (λ d → interpDesc (D d) b)) i)
    --     → PathP (λ iv → W̃ (Arg (λ d → interpDesc (D d) b)) (i≡j iv)) x (transportIndexμ D b i j x)
    -- transportIndexPathP D b i j i≡j x = {!!}


--     {-# BUILTIN REWRITE _≡_ #-}
--     {-# REWRITE toApproxExactResponseD toApproxExactCommandD #-}

    toApproxDesc {Y = Y} D b (FC com res) φ =
      FC
        (toApproxCommandD ⦃ æ = Exact ⦄ D b com)
        λ r →
          let
            ret = φ (toExactResponseD D b (toApproxCommandD ⦃ Exact ⦄ {_} {_} D b com) r)
          in ret
            -- subst
            --   (λ r → Y (inextD D b (toApproxCommandD {{æ = Exact}} D i b com) r))
            --   (toApproxExactResponseD D b _ r)
            --   ret -- {!λ r → Y (inextD D b com r)!} {!!} {!!}
          -- transport (cong₂ (λ c r → Y (inextD D b c r)) refl (toApproxExactResponseD D b _ r)) ret

    toExactDesc {Y = Y} D b (FC com res) φ =
      FC (toExactCommandD D b com)
      λ r →
          let
            ret = φ (toApproxResponseD ⦃ æ = Exact ⦄ D b _
              (transport (congPath (ResponseD ⦃ æ = _ ⦄ D b) (toApproxExactCommandD D b com)) r))
          in ret
            -- transport
            --   (cong₂ (λ c r → Y (inextD D b c (toApproxResponseD {{æ = Exact}} D b c r)))
            --   (symPath (toApproxExactCommandD D i b com))
            --   (symP (toPathP refl))) ret

    open import Cubical.Functions.FunExtEquiv using (funExtDep)



    toApproxμ tyCtor cB Ds b W⁇ = W⁇
    toApproxμ tyCtor cB Ds b W℧ = W℧
    toApproxμ tyCtor cB Ds b (Wsup (FC (d , com) resp)) = Wsup (FC (d , ⟦_⟧F.command recVal) (⟦_⟧F.response recVal))
      module Aμ where
        recVal =
          toApproxDesc
          {X = λ j → W̃ (Arg (λ d → interpDesc {{æ = Exact}} (Ds d) b)) j}
          {Y = λ j → W̃ (Arg (λ d → interpDesc {{æ = Approx}} (Ds d) b)) j}
          (Ds d)
          b
          (FC com resp)
          (λ r → toApproxμ tyCtor cB (λ d₁ → Ds d₁) b (resp r))
    toExactμ tyCtor cB Ds b W⁇ = W⁇
    toExactμ tyCtor cB Ds b W℧ = W℧
    toExactμ tyCtor cB Ds b (Wsup (FC (d , com) resp)) = Wsup (FC (d , ⟦_⟧F.command recVal) (⟦_⟧F.response recVal))
      module Eμ where
        recVal =
          toExactDesc
          {X = λ j → W̃ (Arg (λ d → interpDesc {{æ = Approx}} (Ds d) b)) j}
          {Y = λ j → W̃ (Arg (λ d → interpDesc {{æ = Exact}} (Ds d) b)) j}
          (Ds d)
          b
          (FC com resp)
          (λ r → toExactμ tyCtor cB (λ d₁ → Ds d₁) b (resp r))


    WPathP :
      ∀ {{æ : Æ}} { cB } {tyCtor : CName}
        → { Ds : (d : DName tyCtor) → ℂDesc cB (indSkeleton tyCtor d) }
        → { b : ApproxEl cB }
        → { d : DName tyCtor }
        → {com1 com2 : CommandD (Ds d) b}
        → {res1 : (r : ResponseD (Ds d) b (toApproxCommandD (Ds d) b com1)) → W̃ (Arg (λ d → interpDesc (Ds d) b)) tt }
        → {res2 : (r : ResponseD (Ds d) b (toApproxCommandD (Ds d) b com2)) → W̃ (Arg (λ d → interpDesc (Ds d) b)) tt }
        → (eqc : com1 ≡c com2)
        → (eqr :
               ∀ ( x₀ : ResponseD (Ds d) b (toApproxCommandD (Ds d) b com1) )
               ( x₁ : ResponseD (Ds d) b (toApproxCommandD (Ds d) b com2) )
              (p
              : PathP
                (λ z → ResponseD (Ds d) b (toApproxCommandD (Ds d) b (eqc z))) x₀
                x₁) →
              PathP (λ i₁ →
                W̃ (Arg (λ d₁ → interpDesc (Ds d₁) b))
                (inext (interpDesc (Ds d) b) (eqc i₁) (p i₁)))
              (res1 x₀) (res2 x₁)
          )
        → _≡c_ {A = W̃ (Arg (λ d → interpDesc (Ds d) b)) tt }
          (Wsup (FC (d , com1) res1 ))
          (Wsup (FC (d , com2) res2 ))
    WPathP {Ds = Ds} {b = b} {d = d} {com1 = com1} {com2 = com2} {res1 = res1} {res2 = res2}
      eqc eqr =
        cong₂ {B = λ c → (r : ResponseD {{æ = _}} (Ds d) b (toApproxCommandD (Ds d) b c)) → _}
          {x = com1} {y = com2}
          (λ c r → Wsup (FC (d , c) r) )
          eqc
          {u = res1} {v = res2}
          (funExtDep (λ {x} {x1} pth → eqr x x1 pth))


    toApproxExactμ tyCtor cB Ds b W℧ = reflc
    toApproxExactμ tyCtor cB Ds b W⁇ = reflc
    toApproxExactμ tyCtor cB Ds b (Wsup (FC (d , com) resp)) = WPathP {{æ = Approx}}
      (toApproxExactCommandD (Ds d) b com)
      λ r1 r2 pth → congPath (toApproxμ tyCtor cB Ds b) (congPath (toExactμ tyCtor cB Ds b) (congPath resp
        (congPath (toApproxResponseD ⦃ æ = _ ⦄ (Ds d) b com) (fromPathP (cong₂ (toExactResponseD (Ds d) b) (toApproxExactCommandD (Ds d) b com) pth))
        ∙ toApproxExactResponseD (Ds d) b (toApproxCommandD {{æ = _}} (Ds d) b com) r2))) ▷ (toApproxExactμ tyCtor cB (λ d₁ → Ds d₁) b (resp r2))




-- We can then recursively build the codes for each level
-- We take a guarded fixed-point, so we can have a code CSelf such that
-- El CSelf = ℂ
-- This gives us a version of Girard's Paradox that is safely stowed behind the guarded modality
CodeModuleAt : ∀  ℓ →  CodeModule ℓ
CodeModuleAt zero = --G.fix λ ModSelf →
  codeModule (record
                { ℂ-1 = 𝟘
                ; El-1 = λ ()
                ; toApprox-1 = λ ()
                ; toExact-1 = λ ()
                ; toApproxExact-1 = λ ()
                }
                )
CodeModuleAt (suc ℓ) = codeModule (SmallerCodeFor (CodeModuleAt ℓ))
  where
    SmallerCodeFor : ∀ {ℓ} → CodeModule ℓ → SmallerCode
    SmallerCodeFor CM = record
                        { ℂ-1 = ℂ
                        ; El-1 = El
                        ; toApprox-1 = toApprox
                        ; toExact-1 = toExact
                        ; toApproxExact-1 = toApproxExact
                        }
                  where open CodeModule CM

SmallerCodeAt : ℕ → SmallerCode
SmallerCodeAt ℓ = CodeModule.sc (CodeModuleAt ℓ)

ℂ-1>0 : ∀ {ℓ} → ℂ-1 (SmallerCodeAt ℓ) → 0< ℓ
ℂ-1>0 {ℓ = zero} ()
ℂ-1>0 {ℓ = suc ℓ} c = suc<

-- -- If we have smaller codes, ℓ > 0
-- ℓsuc : ∀ {ℓ} → CodeModule.ℂ-1 (CodeModuleAt ℓ) → Σ[ ℓ' ∈ ℕ ](ℓ ≡p suc ℓ')
-- ℓsuc {suc ℓ} x = _ , reflp

-- Expose each value in the Code module with implicit level ℓ
-- Except for ℂ and ⁇, which each need an explicit level
module CIMod {ℓ} where
  open CodeModule (CodeModuleAt ℓ) public hiding (ℂ ; ⁇ )

open CIMod public

-- Make the levels explicit for each code
ℂ : ℕ → Set
ℂ ℓ = CodeModule.ℂ (CodeModuleAt ℓ)

⁇Ty : ∀ {{_ : Æ}} ℓ → Set
⁇Ty {{æ}} ℓ = (CodeModule.⁇ (CodeModuleAt ℓ) {{æ}})

⁇lob : ∀ {{ _ : Æ }} {ℓ} → ⁇Ty ℓ ≡ F⁇ {ℓ} (A.next (⁇Rec {ℓ = ℓ}))
⁇lob {ℓ} = congPath F⁇ (A.pfix _)



unfold⁇ : ∀ {{_ : Æ}} {ℓ} → ⁇Ty ℓ →  F⁇ (A.next (⁇Rec {ℓ = ℓ}))
unfold⁇ {ℓ} x = subst (λ x → x) ⁇lob x


fold⁇ : ∀ {{_ : Æ}} {ℓ} →  F⁇ (A.next (⁇Rec {ℓ = ℓ}))  → ⁇Ty ℓ
fold⁇ {ℓ} x = subst (λ x → x) (sym ⁇lob) x


-- ℂ-1>0 : ∀ {ℓ} → ℂ-1 {ℓ = ℓ} → 0< ℓ
-- ℂ-1>0 {suc ℓ} x = suc<

-- -- The least precise argument to a guarded function from ⁇ to ⁇
-- -- Used for checking if functions are errors
-- -- topArg : ∀ {ℓ} → ▸ map▹ ⁇Self (dfix (λ args → selfRec (F⁇ {ℓ} args) ⁇℧))
-- -- topArg {ℓ} = Dep▸ ℧Self (dfix (λ args → selfRec (F⁇ {ℓ} args) ⁇℧))



-- -- Relation for whether a value is an error in type ⁇
-- -- data ℧≡ {ℓ} : ⁇Ty ℓ → Set where
-- --          ℧℧ : ℧≡ ⁇℧
-- --          ⁇Π℧ : ∀ {f} → ⁇℧ ≡ f topArg  → ℧≡ (⁇Π f)
-- --          -- ⁇Π℧ : ∀ {f : ▸ map▹ ⁇Self Self → F⁇ Self  } → ⁇℧ ≡ f (λ tic → ℧Self (Self tic))  → ℧≡ (⁇Π f)
-- --          ⁇Type℧ : {{_ : 0< ℓ}} → ℧≡ (⁇Type ℧-1)
-- --          ⁇Σ℧ : ℧≡ (⁇Σ (⁇℧ , ⁇℧))
-- --          ⁇≡℧ : ℧≡ (⁇≡ ⁇℧)
-- --          ⁇μ℧ : ∀ (tyCtor : CName) (ctor : DName tyCtor)
-- --            → ℧≡ (⁇μ tyCtor ctor μ℧)


-- Every type has an error element
℧ : ∀ {{æ : Æ}} {ℓ} → (c : ℂ ℓ)  → El c
℧ CodeModule.C⁇ = ⁇℧
℧ CodeModule.C℧ = ℧𝟘
℧ CodeModule.C𝟘 = tt
℧ CodeModule.C𝟙 = ℧𝟙
℧ {suc ℓ} CodeModule.CType = C℧
℧ (CodeModule.CΠ dom cod) = λ x → (℧ (cod (approx x)))
℧ (CodeModule.CΣ dom cod)  = ℧ dom , ℧ (cod (CodeModule.approx (CodeModuleAt _) (℧ dom)))
--withApprox (λ æ₁ → ℧ ⦃ æ₁ ⦄ dom) , ℧ (cod _)
-- ℧ (CodeModule.CΣ dom cod) ⦃ Exact ⦄ = (℧ dom {{Approx}} , ℧ dom {{Exact}}) , ℧ (cod (℧ dom {{Approx}})) {{Exact}}
℧ (CodeModule.C≡ c x y) = ℧ {{Approx}} c ⊢ x ≅ y
℧ (CodeModule.Cμ tyCtor c D x) = W℧
℧ {ℓ = suc ℓ} (CCumul c) = ℧ c

℧Approx : ∀ {ℓ} (c : ℂ ℓ) → ApproxEl c
℧Approx = ℧ {{Approx}}

-- ℧Approxed : ∀ {{æ : Æ}} {ℓ} (c : ℂ ℓ) → El c
-- ℧Approxed c = withApprox λ æ → ℧ {{æ = æ}} c


DCtors : ∀ {ℓ} → CName → Set
DCtors {ℓ} tyCtor = (d : DName tyCtor) → ℂDesc {ℓ = ℓ} C𝟙 (indSkeleton tyCtor d)


▹⁇Self : {{æ : Æ}} →  ℕ → A.▹ ⁇Self
▹⁇Self {{æ = æ}} ℓ = A.dfix (▹⁇Rec {ℓ = ℓ})

▹⁇RecE : ∀ ℓ →  G.▹ ⁇Self → ⁇Self
▹⁇RecE ℓ x = ▹⁇Rec {ℓ = ℓ} {{æ = Exact}} x




▹⁇Self≡ : ∀ {{æ : Æ}} {ℓ} → ▹⁇Self ℓ ≡ A.next (⁇Rec {ℓ = ℓ})
▹⁇Self≡ = A.pfix (CodeModule.▹⁇Rec (CodeModuleAt _))

▹⁇ : {{æ : Æ}} →  ℕ → A.▹ Set
▹⁇ ℓ = A.map▹ ⁇TySelf  (▹⁇Self ℓ)

▹⁇≡ : ∀ {{æ : Æ}} {ℓ} → ▹⁇ ℓ ≡ A.next (⁇Ty ℓ)
▹⁇≡ ⦃ æ = Approx ⦄ {ℓ = ℓ} = refl
▹⁇≡ ⦃ æ = Exact ⦄ {ℓ = ℓ} = congPath (G.map▹ ⁇TySelf) (▹⁇Self≡ {{æ = Exact}}) ∙ G.mapNext ⁇TySelf _

⁇Wrap≡ : ∀ {{æ  : Æ}} {ℓ} → A.▸ (▹⁇ ℓ) ≡c (A.▹ (⁇Ty ℓ))
⁇Wrap≡ {{æ = Exact}} = G.later-extSwap (λ α → pfixSelf' α)
  where
    pfixSelf' : ∀ {ℓ} →  G.▸ \ α → ( ⁇TySelf (G.dfix (▹⁇RecE ℓ) α) ≡ ⁇TySelf (▹⁇RecE ℓ (G.dfix (▹⁇RecE ℓ))))
    pfixSelf' tic = cong ⁇TySelf (G.pfix' (▹⁇RecE _) tic)
⁇Wrap≡ {{æ = Approx}} = reflc

apply⁇Fun : ∀ {{æ : Æ}} {ℓ} → (▹⁇Ty (▹⁇Self ℓ) → ⁇Ty ℓ) → ⁇Ty ℓ → ⁇Ty ℓ
apply⁇Fun {ℓ = ℓ} f x =
  let
    foo : ⁇Ty ℓ
    foo = ⁇Π f
  in f (transport (symPath ⁇Wrap≡) (A.next x))


-- apply▸ : ∀ {{_ : Æ}} {ℓ} (f : (A.▸ (A.dfix (F⁇ {ℓ = ℓ}))) → ⁇Ty ℓ) → (x : A.▹ (⁇Ty ℓ)) →  ⁇Ty ℓ
-- apply▸ f x = f (transport (cong A.▹_ (⁇lob ∙ cong F⁇ (sym ▹⁇≡)) ∙ sym A.hollowEq ) x)

WUnk : ∀ {{æ : Æ}} → ℕ → Set
WUnk ℓ = (FWUnk {ℓ = ℓ} (▹⁇Self ℓ))

⁇ToW : ∀ {{æ : Æ}} {ℓ} → ⁇Ty ℓ → WUnk ℓ
⁇ToW ⁇⁇ = W⁇
⁇ToW ⁇℧ = W℧
⁇ToW ⁇𝟙 = Wsup (FC ( H𝟙 , tt) λ ())
⁇ToW {ℓ = suc ℓ} (⁇Type ty) = Wsup (FC ( HType , ty) λ ())
⁇ToW {ℓ = suc ℓ} (⁇Cumul c x) = Wsup (FC ( HCumul , (c , x)) λ ())
⁇ToW (⁇Π f) = Wsup (FC ( HΠ , tt) λ x → ⁇ToW (f x))
⁇ToW (⁇Σ (x , y)) = Wsup (FC ( HΣ , tt) λ r → if r then ⁇ToW x else ⁇ToW y)
⁇ToW (⁇≡ (x ⊢ _ ≅ _)) = Wsup (FC ( H≅ , tt) λ _ → ⁇ToW x)
⁇ToW (⁇μ tyCtor x) = Wsup (FC ( (HCtor tyCtor) , tt) λ _ → x)


⁇FromW : ∀ {{æ : Æ}} {ℓ} → WUnk ℓ → ⁇Ty ℓ
⁇FromW (Wsup (FC (HΠ , arg) res)) = ⁇Π (λ x → ⁇FromW (res x))
⁇FromW (Wsup (FC (HΣ , arg) res)) = ⁇Σ ((⁇FromW (res true)) , (⁇FromW (res false)))
⁇FromW (Wsup (FC (H≅ , arg) res)) = ⁇≡ ((⁇FromW (res tt)) ⊢ _ ≅ _)
⁇FromW (Wsup (FC (H𝟙 , arg) res)) = ⁇𝟙
⁇FromW {ℓ = suc ℓ} (Wsup (FC (HType , c) res)) = ⁇Type {{inst = suc<}} c
⁇FromW {ℓ = suc ℓ} (Wsup (FC (HCumul , (c , x)) res)) = ⁇Cumul {{inst = suc<}} c x
⁇FromW (Wsup (FC (HCtor tyCtor , arg) res)) = ⁇μ tyCtor (res tt)
⁇FromW W⁇ = ⁇⁇
⁇FromW W℧ = ⁇℧

⁇IsoWL : ∀ {{æ : Æ}} {ℓ} → (x : ⁇Ty ℓ) → ⁇FromW (⁇ToW x) ≡ x
⁇IsoWL ⁇⁇ = reflc
⁇IsoWL ⁇℧ = reflc
⁇IsoWL ⁇𝟙 = reflc
⁇IsoWL {ℓ = suc ℓ} (⁇Type ⦃ inst = suc< {ℓ = .ℓ} ⦄ x) = reflc
⁇IsoWL {ℓ = suc ℓ} (⁇Cumul ⦃ inst = suc< {ℓ = .ℓ} ⦄ c x) = reflc
⁇IsoWL (⁇Π f) = cong ⁇Π (funExt λ x → ⁇IsoWL (f x))
⁇IsoWL (⁇Σ (x , y)) = cong₂ (λ x y → ⁇Σ (x , y)) (⁇IsoWL x) (⁇IsoWL y)
⁇IsoWL (CodeModule.⁇≡ (x ⊢ .⁇⁇ ≅ .⁇⁇)) = cong (λ x → ⁇≡ (x ⊢ _ ≅ _)) (⁇IsoWL x)
⁇IsoWL (⁇μ tyCtor x) = reflc

Wsup-cong : ∀ {I} {C : Container I} {i : I} → {com : Command C i} → {x y : (res : Response C com) → W̃ C (inext C com res)} → x ≡ y → Wsup (FC com x) ≡c Wsup (FC com y)
Wsup-cong {com = com} {x = x} {y = y} pf = cong {x = x} {y = y} (λ x → Wsup (FC _ x)) pf

⁇IsoWR : ∀ {{æ : Æ}} {ℓ} (x : WUnk ℓ)  → ⁇ToW (⁇FromW x) ≡ x
⁇IsoWR (Wsup (FC (HΠ , tt) f)) = Wsup-cong (funExt λ x → ⁇IsoWR (f x))
⁇IsoWR (Wsup (FC (HΣ , tt) res)) = Wsup-cong (funExt (λ {true → ⁇IsoWR (res true) ; false → ⁇IsoWR (res false)}))
⁇IsoWR (Wsup (FC (H≅ , arg) res)) = Wsup-cong (funExt (λ (tt) → ⁇IsoWR (res tt)))
⁇IsoWR (Wsup (FC (H𝟙 , arg) res)) = Wsup-cong (funExt (λ ()))
⁇IsoWR {ℓ = suc ℓ} (Wsup (FC (HType , arg) res)) = Wsup-cong (funExt λ ())
⁇IsoWR {ℓ = suc ℓ} (Wsup (FC (HCumul , arg) res)) = Wsup-cong (funExt λ ())
⁇IsoWR (Wsup (FC (HCtor x , arg) res)) = Wsup-cong (funExt (λ x → reflc))
⁇IsoWR W℧ = reflc
⁇IsoWR W⁇ = reflc


⁇DescIso : ∀ {{_ : Æ}} {ℓ} → Iso (⁇Ty ℓ) (WUnk ℓ)
⁇DescIso = iso ⁇ToW ⁇FromW ⁇IsoWR ⁇IsoWL

