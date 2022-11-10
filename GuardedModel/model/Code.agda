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

open import ApproxExact using (Approx ; Exact ; Æ ;   withApprox)

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
    ℂ-1 : Set
    El-1 : {{æ : Æ}} → ℂ-1 -> Set
    toApprox-1 : (c : ℂ-1) -> El-1 {{æ = Exact}} c → El-1 {{æ = Approx}} c
    toExact-1 : (c : ℂ-1) -> El-1 {{æ = Approx}} c → El-1 {{æ = Exact}} c
    -- ⁇-1 : {{_ : Æ}} → Set
    -- ℧-1 : {{_ : 0< ℓ}} →  ℂ-1
    -- ℂSelf : ▹ Set


    ---------------------------------------------------------------------
    ----------- The Unknown Type ----------------------------------------
    -- The Functor describing the unknown type ⁇
    -- We write it as a HIT to make sure all of the error values are equal
  data F⁇ {{ æ : Æ }} (Self : A.▹ Type) :  Set where
      ⁇℧ : F⁇ Self
      ⁇⁇ : F⁇ Self
      ⁇𝟙 : F⁇ Self
      ⁇Type : {{ inst : 0< ℓ }} → ℂ-1 → F⁇ Self
      ⁇Cumul :  {{ inst : 0< ℓ }} → (c : ℂ-1) → El-1 c → F⁇ Self
      -- This is where ⁇ is a non-positive type: The germ of Π is ⁇ → ⁇
      -- So we need to guard the use of ⁇ in the domain
      ⁇Π : (A.▸ Self →  (F⁇ Self )) → F⁇ Self
      -- The germ of pairs is a pair of ⁇s
      ⁇Σ : (F⁇ Self  × F⁇ Self ) → F⁇ Self
      -- The germ of an equality type is a witness of equality between two ⁇s
      -- TODO: is there a way to make the witness approx?
      ⁇≡ : _≅_ {A = F⁇ Self} ⁇⁇ ⁇⁇ → F⁇ Self
      -- TODO: right now, must approximate taking the germ of inductives that use their parameters in dependent ways
      -- e.g. data NotProp A where np : (a b : A) → a ≠ b → NotProp A
      -- It's unclear whether we can use Induction-Induction to do this in a strictly-positive way
      ⁇μ : (tyCtor : CName) → (x : FPreGerm ℓ ℂ-1 El-1 Self tyCtor) →  F⁇ Self
      -- ⁇μ : (tyCtor : CName) → (x : FPreGerm ℓ tyCtor Self (F⁇ Self)) →  F⁇ Self
    -- The unknown type, i.e. the fixed-point of F⁇
  ⁇ : {{æ : Æ}} → Set
  -- ⁇ Is the guarded fixed point of F⁇
  ⁇ = A.fix F⁇

  -- Approximating/embedding for the unknown type
  toApprox⁇ : ⁇ {{æ = Exact}} → ⁇ {{æ = Approx}}
  toExact⁇ : ⁇ {{æ = Approx}} → ⁇ {{æ = Exact}}

  toApprox⁇ ⁇℧ = ⁇℧
  toApprox⁇ ⁇⁇ = ⁇⁇
  toApprox⁇ ⁇𝟙 = ⁇𝟙
  toApprox⁇ (⁇Type x) = ⁇Type x
  toApprox⁇ (⁇Cumul c x) = ⁇Cumul c (toApprox-1 c x)
  -- This is where we really need to approx: we have a guarded function,
  -- so we take its upper limit by giving it ⁇ as an argument
  toApprox⁇ (⁇Π f) = ⁇Π (λ _ → toApprox⁇ (f (transport⁻ G.hollowEq (G.next (⁇⁇ {{æ = Exact}})))))
  toApprox⁇ (⁇Σ (x , y)) = ⁇Σ (toApprox⁇ x , toApprox⁇ y)
  toApprox⁇ (⁇≡ (w ⊢ x ≅ y )) = ⁇≡ (toApprox⁇ w ⊢ toApprox⁇ x ≅ toApprox⁇ y)
  toApprox⁇ (⁇μ tyCtor x) = {!!}

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
    interpDesc : ∀ {{æ : Æ}} {I} {cB} {sig} →  (ℂDesc I cB sig) → ApproxEl cB → Container (ApproxEl I)
    CommandD : ∀ {{_ : Æ}}  {I cB sig} → ℂDesc I cB sig → ApproxEl I → (ApproxEl cB → Set)
    ResponseD : ∀ {{_ :  Æ}} {I cB sig} → (D : ℂDesc I cB sig) → ∀ {i : ApproxEl I} → (b : ApproxEl cB) → CommandD D i b → Set
    inextD : ∀ {{_ : Æ}} {I cB sig} → (D : ℂDesc I cB sig) → ∀ {i} → (b : ApproxEl cB) → (c : CommandD D i b) → ResponseD D b c → ApproxEl  I
    FWUnk : {{_ : Æ}} → A.▹ Set → Set
    -- ▹interpDesc : ∀{{ _ : Æ }} {I} → (ℂDesc I ) → Container 𝟙
    -- ▹CommandD : ∀ {{ _ : Æ }}{I} →  ℂDesc I  → Set
    -- ▹ResponseD : ∀ {{ _ : Æ }}{I} →  (D : ℂDesc I ) → ▹CommandD D → Set


    toApproxDesc : ∀  {I} {cB} {sig} →  (D : ℂDesc I cB sig) → (b : ApproxEl cB) (i : ApproxEl I) → W̃  (interpDesc {{æ = Exact}} D b) i → W̃  (interpDesc {{æ = Approx}} D b) i
    toExactDesc : ∀  {I} {cB} {sig} →  (D : ℂDesc I cB sig) → (b : ApproxEl cB) (i : ApproxEl I) → W̃  (interpDesc {{æ = Approx}} D b) i → W̃  (interpDesc {{æ = Exact}} D b) i
    -- toExactDesc : ∀  {I} {cB} {sig} →  (ℂDesc I cB sig) → ApproxEl cB → Container (ApproxEl I)

    ------------------------------- Definitions --------------------

    ----------------------------------------------------------------
    --- Unknown type
    data _ where
      C⁇ : ℂ
    -- The unknown code denotes the unknown type
    El C⁇ = ⁇
    toApprox C⁇ x = {!!}
    toExact C⁇ x = {!!}
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
    El CType = ℂ-1
    toApprox CType x = {!!}
    toExact CType x = {!!}
    -- ▹El CType = ℂ-1
    --
    --For lower universes, we can lift codes to this universe without needing guardedness
    data _ where
      CCumul :  {{ inst : 0< ℓ }} → ℂ-1 → ℂ
      -- ⁇Cumul : ⁇-1 → F⁇ Self
    El (CCumul c) = El-1 c
    toApprox (CCumul c) x = {!!}
    toExact (CCumul c) x = {!!}
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
        → ApproxEl cI → ℂ
    El (Cμ tyCtor cI D i) = W̃ (Arg (λ d → interpDesc (D d) true)) i
    toApprox (Cμ tyCtor cI D i) x = {!!}
    toExact (Cμ tyCtor cI D i) x = {!!}
    -- ▹El (Cμ tyCtor cI D i) = W (Arg (λ d → ▹interpDesc {{Exact}} (D d))) 𝟙 tt


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

    --adapted from https://stackoverflow.com/questions/34334773/why-do-we-need-containers
    interpDesc {I = I} {cB = cB} D b  = (λ i → CommandD D i b) ◃ ResponseD D b / inextD D b
    -- interpDesc D b  = CommandD D b  ◃ ResponseD  D  b  ◃  (λ _ → 𝟘) / inextD D b

    CommandD (CEnd j) i b = i ≅ j
    CommandD (CArg c D _ _) i b = Σ[ a ∈ El (c b) ] CommandD D i (b , approx a)
    CommandD (CRec j D) i b = CommandD D i b
    CommandD (CHRec c j D _ _) i b = CommandD D i b
--     -- CommandD (CHGuard c D E) i =  ((▹ (El c)) → CommandD D i) × CommandD E i

    ResponseD (CEnd i) b com = 𝟘
    ResponseD (CArg c D _ _) b (a , com) = ResponseD D (b , approx a) com
    ResponseD (CRec j D) b com = Rec⇒ 𝟙    Rest⇒ (ResponseD D b com)
    ResponseD (CHRec c j D _ _) b com = Rec⇒ (El (c b) )    Rest⇒ (ResponseD D b com)
    -- ResponseD (CHGuard c D E) (comD , comE) =
    --   GuardedArg⇒ (Σ[ a▹ ∈  ▹ El c ] (ResponseD D (comD a▹)))
    --     Rest⇒ ResponseD E comE


    inextD (CArg c D _ _) {i} b (a , com) res = inextD D (b , approx a) com res
    inextD (CRec j D) {i} b com (Rec x) = j
    inextD (CRec j D) {i} b com (Rest x) = inextD D b com x
    inextD (CHRec c j D _ _) {i} b com (Rec res) = j b (approx res)
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
    FWUnk Self = Pre⁇ ℓ ℂ-1 El-1 Self
-----------------------------------------------------------------------




-- We can then recursively build the codes for each level
-- We take a guarded fixed-point, so we can have a code CSelf such that
-- El CSelf = ℂ
-- This gives us a version of Girard's Paradox that is safely stowed behind the guarded modality
CodeModuleAt : ∀  ℓ →  CodeModule ℓ
CodeModuleAt zero = --G.fix λ ModSelf →
  record
    { ℂ-1 = 𝟘
    ; El-1 = λ ()
    -- ; ⁇-1 = 𝟘
    -- ; ℧-1 = λ { {{()}} }
    -- ; ℂSelf = map▹ CodeModule.ℂ ModSelf
    }
CodeModuleAt (suc ℓ) = -- G.fix λ ModSelf →
  record
    { ℂ-1 = CodeModule.ℂ (CodeModuleAt ℓ)
    ; El-1 = λ x → CodeModule.El (CodeModuleAt ℓ) x
    -- ; ⁇-1 = CodeModule.⁇ (CodeModuleAt ℓ)
    -- ; ℧-1 = CodeModule.ℂ.C℧
    -- ; ℂSelf = map▹ CodeModule.ℂ ModSelf
    }


-- If we have smaller codes, ℓ > 0
ℓsuc : ∀ {ℓ} → CodeModule.ℂ-1 (CodeModuleAt ℓ) → Σ[ ℓ' ∈ ℕ ](ℓ ≡p suc ℓ')
ℓsuc {suc ℓ} x = _ , reflp

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


⁇lob : ∀ {{ _ : Æ }} {ℓ} → ⁇Ty ℓ ≡ F⁇ {ℓ} (A.next (⁇Ty ℓ))
⁇lob {ℓ} = cong (λ P → F⁇ {ℓ} P) (A.pfix (F⁇ {ℓ}))



unfold⁇ : ∀ {{_ : Æ}} {ℓ} → ⁇Ty ℓ →  F⁇ (A.next (⁇Ty ℓ))
unfold⁇ {ℓ} x = subst (λ x → x) ⁇lob x


fold⁇ : ∀ {{_ : Æ}} {ℓ} →  F⁇ (A.next (⁇Ty ℓ))  → ⁇Ty ℓ
fold⁇ {ℓ} x = subst (λ x → x) (sym ⁇lob) x


ℂ-1>0 : ∀ {ℓ} → ℂ-1 {ℓ = ℓ} → 0< ℓ
ℂ-1>0 {suc ℓ} x = suc<

-- The least precise argument to a guarded function from ⁇ to ⁇
-- Used for checking if functions are errors
-- topArg : ∀ {ℓ} → ▸ map▹ ⁇Self (dfix (λ args → selfRec (F⁇ {ℓ} args) ⁇℧))
-- topArg {ℓ} = Dep▸ ℧Self (dfix (λ args → selfRec (F⁇ {ℓ} args) ⁇℧))



-- Relation for whether a value is an error in type ⁇
-- data ℧≡ {ℓ} : ⁇Ty ℓ → Set where
--          ℧℧ : ℧≡ ⁇℧
--          ⁇Π℧ : ∀ {f} → ⁇℧ ≡ f topArg  → ℧≡ (⁇Π f)
--          -- ⁇Π℧ : ∀ {f : ▸ map▹ ⁇Self Self → F⁇ Self  } → ⁇℧ ≡ f (λ tic → ℧Self (Self tic))  → ℧≡ (⁇Π f)
--          ⁇Type℧ : {{_ : 0< ℓ}} → ℧≡ (⁇Type ℧-1)
--          ⁇Σ℧ : ℧≡ (⁇Σ (⁇℧ , ⁇℧))
--          ⁇≡℧ : ℧≡ (⁇≡ ⁇℧)
--          ⁇μ℧ : ∀ (tyCtor : CName) (ctor : DName tyCtor)
--            → ℧≡ (⁇μ tyCtor ctor μ℧)


-- -- Every type has an error element
-- ℧ : ∀ {{æ : Æ}} {ℓ} → (c : ℂ ℓ)  → El c
-- ℧ CodeModule.C⁇ = ⁇℧
-- ℧ CodeModule.C℧ = tt
-- ℧ CodeModule.C𝟘 = tt
-- ℧ CodeModule.C𝟙 = false
-- ℧ {suc ℓ} CodeModule.CType = C℧
-- ℧ (CodeModule.CΠ dom cod) = λ x → (℧ (cod (approx x)))
-- ℧ (CodeModule.CΣ dom cod)  = ℧ dom , ℧ (cod (CodeModule.approx (CodeModuleAt _) (℧ dom)))
-- --withApprox (λ æ₁ → ℧ ⦃ æ₁ ⦄ dom) , ℧ (cod _)
-- -- ℧ (CodeModule.CΣ dom cod) ⦃ Exact ⦄ = (℧ dom {{Approx}} , ℧ dom {{Exact}}) , ℧ (cod (℧ dom {{Approx}})) {{Exact}}
-- ℧ (CodeModule.C≡ c x y) = ℧ {{Approx}} c ⊢ x ≅ y
-- ℧ (CodeModule.Cμ tyCtor c D x) = W℧
-- ℧ {ℓ = suc ℓ} (CCumul c) = ℧ c

-- ℧Approx : ∀ {ℓ} (c : ℂ ℓ) → ApproxEl c
-- ℧Approx = ℧ {{Approx}}

-- -- ℧Approxed : ∀ {{æ : Æ}} {ℓ} (c : ℂ ℓ) → El c
-- -- ℧Approxed c = withApprox λ æ → ℧ {{æ = æ}} c


-- DCtors : ∀ {ℓ} → CName → ℂ ℓ → Set
-- DCtors tyCtor cI = (d : DName tyCtor) → ℂDesc cI C𝟘 (indSkeleton tyCtor d)

-- ▹⁇ : {{_ : Æ}} →  ℕ → A.▹ Set
-- ▹⁇ ℓ = A.dfix (F⁇ {ℓ})

-- ▹⁇≡ : ∀ {{_ : Æ}} {ℓ} → ▹⁇ ℓ ≡ A.next (⁇Ty ℓ)
-- ▹⁇≡ = A.pfix F⁇

-- apply▸ : ∀ {{_ : Æ}} {ℓ} (f : (A.▸ (A.dfix (F⁇ {ℓ = ℓ}))) → ⁇Ty ℓ) → (x : A.▹ (⁇Ty ℓ)) →  ⁇Ty ℓ
-- apply▸ f x = f (transport (cong A.▹_ (⁇lob ∙ cong F⁇ (sym ▹⁇≡)) ∙ sym A.hollowEq ) x)

-- WUnk : ∀ {{æ : Æ}} → ℕ → Set
-- WUnk ℓ = (FWUnk {ℓ = ℓ} (▹⁇ ℓ))

-- ⁇ToW : ∀ {{æ : Æ}} {ℓ} → ⁇Ty ℓ → WUnk ℓ
-- ⁇ToW ⁇⁇ = W⁇
-- ⁇ToW ⁇℧ = W℧
-- ⁇ToW ⁇𝟙 = Wsup (FC ( H𝟙 , tt) λ ())
-- ⁇ToW {ℓ = suc ℓ} (⁇Type ty) = Wsup (FC ( HType , ty) λ ())
-- ⁇ToW {ℓ = suc ℓ} (⁇Cumul c x) = Wsup (FC ( HCumul , (c , x)) λ ())
-- ⁇ToW (⁇Π f) = Wsup (FC ( HΠ , tt) λ x → ⁇ToW (f x))
-- ⁇ToW (⁇Σ (x , y)) = Wsup (FC ( HΣ , tt) λ r → if r then ⁇ToW x else ⁇ToW y)
-- ⁇ToW (⁇≡ (x ⊢ _ ≅ _)) = Wsup (FC ( H≅ , tt) λ _ → ⁇ToW x)
-- ⁇ToW (⁇μ tyCtor x) = Wsup (FC ( (HCtor tyCtor) , tt) λ _ → x)


-- ⁇FromW : ∀ {{æ : Æ}} {ℓ} → WUnk ℓ → ⁇Ty ℓ
-- ⁇FromW (Wsup (FC (HΠ , arg) res)) = ⁇Π (λ x → ⁇FromW (res x))
-- ⁇FromW (Wsup (FC (HΣ , arg) res)) = ⁇Σ ((⁇FromW (res true)) , (⁇FromW (res false)))
-- ⁇FromW (Wsup (FC (H≅ , arg) res)) = ⁇≡ ((⁇FromW (res tt)) ⊢ _ ≅ _)
-- ⁇FromW (Wsup (FC (H𝟙 , arg) res)) = ⁇𝟙
-- ⁇FromW {ℓ = suc ℓ} (Wsup (FC (HType , c) res)) = ⁇Type {{inst = suc<}} c
-- ⁇FromW {ℓ = suc ℓ} (Wsup (FC (HCumul , (c , x)) res)) = ⁇Cumul {{inst = suc<}} c x
-- ⁇FromW (Wsup (FC (HCtor tyCtor , arg) res)) = ⁇μ tyCtor (res tt)
-- ⁇FromW W⁇ = ⁇⁇
-- ⁇FromW W℧ = ⁇℧

-- ⁇IsoWL : ∀ {{æ : Æ}} {ℓ} → (x : ⁇Ty ℓ) → ⁇FromW (⁇ToW x) ≡ x
-- ⁇IsoWL ⁇⁇ = reflc
-- ⁇IsoWL ⁇℧ = reflc
-- ⁇IsoWL ⁇𝟙 = reflc
-- ⁇IsoWL {ℓ = suc ℓ} (⁇Type ⦃ inst = suc< {ℓ = .ℓ} ⦄ x) = reflc
-- ⁇IsoWL {ℓ = suc ℓ} (⁇Cumul ⦃ inst = suc< {ℓ = .ℓ} ⦄ c x) = reflc
-- ⁇IsoWL (⁇Π f) = cong ⁇Π (funExt λ x → ⁇IsoWL (f x))
-- ⁇IsoWL (⁇Σ (x , y)) = cong₂ (λ x y → ⁇Σ (x , y)) (⁇IsoWL x) (⁇IsoWL y)
-- ⁇IsoWL (CodeModule.⁇≡ (x ⊢ .⁇⁇ ≅ .⁇⁇)) = cong (λ x → ⁇≡ (x ⊢ _ ≅ _)) (⁇IsoWL x)
-- ⁇IsoWL (⁇μ tyCtor x) = reflc

-- Wsup-cong : ∀ {I} {C : Container I} {i : I} → {com : Command C i} → {x y : (res : Response C com) → W̃ C (inext C com res)} → x ≡ y → Wsup (FC com x) ≡c Wsup (FC com y)
-- Wsup-cong {com = com} {x = x} {y = y} pf = cong {x = x} {y = y} (λ x → Wsup (FC _ x)) pf

-- ⁇IsoWR : ∀ {{æ : Æ}} {ℓ} (x : WUnk ℓ)  → ⁇ToW (⁇FromW x) ≡ x
-- ⁇IsoWR (Wsup (FC (HΠ , tt) f)) = Wsup-cong (funExt λ x → ⁇IsoWR (f x))
-- ⁇IsoWR (Wsup (FC (HΣ , tt) res)) = Wsup-cong (funExt (λ {true → ⁇IsoWR (res true) ; false → ⁇IsoWR (res false)}))
-- ⁇IsoWR (Wsup (FC (H≅ , arg) res)) = Wsup-cong (funExt (λ (tt) → ⁇IsoWR (res tt)))
-- ⁇IsoWR (Wsup (FC (H𝟙 , arg) res)) = Wsup-cong (funExt (λ ()))
-- ⁇IsoWR {ℓ = suc ℓ} (Wsup (FC (HType , arg) res)) = Wsup-cong (funExt λ ())
-- ⁇IsoWR {ℓ = suc ℓ} (Wsup (FC (HCumul , arg) res)) = Wsup-cong (funExt λ ())
-- ⁇IsoWR (Wsup (FC (HCtor x , arg) res)) = Wsup-cong (funExt (λ x → reflc))
-- ⁇IsoWR W℧ = reflc
-- ⁇IsoWR W⁇ = reflc


-- ⁇DescIso : ∀ {{_ : Æ}} {ℓ} → Iso (⁇Ty ℓ) (WUnk ℓ)
-- ⁇DescIso = iso ⁇ToW ⁇FromW ⁇IsoWR ⁇IsoWL

-- -- -- ⁇ : ∀ {ℓ} → (c : ℂ ℓ) → {{æ : Æ}} → El c
-- -- -- ⁇ CodeModule.C⁇ = ⁇⁇
-- -- -- ⁇ CodeModule.C℧ = tt
-- -- -- ⁇ CodeModule.C𝟘 = tt
-- -- -- ⁇ CodeModule.C𝟙 = false
-- -- -- ⁇ {suc ℓ} CodeModule.CType = C⁇
-- -- -- ⁇ (CodeModule.CΠ dom cod) = λ x → (⁇ (cod (approx x)))
-- -- -- ⁇ (CodeModule.CΣ dom cod)  = pairWithApprox (⁇ dom {{Approx}}) (⁇ dom ) , ⁇ (cod _)
-- -- -- -- ⁇ (CodeModule.CΣ dom cod) ⦃ Exact ⦄ = (⁇ dom {{Approx}} , ⁇ dom {{Exact}}) , ⁇ (cod (⁇ dom {{Approx}})) {{Exact}}
-- -- -- ⁇ (CodeModule.C≡ c x y) = ⁇⊢ x ≅ y
-- -- -- ⁇ (CodeModule.Cμ tyCtor c D x) = W⁇

-- -- -- {-# DISPLAY CodeModule.ℂ _ = ℂ  #-}
-- -- -- {-# DISPLAY CodeModule.El _  = El  #-}



-- -- -- -- -- Lift a code to a higher universe
-- -- -- -- liftℂ : ∀ {j k} → j ≤ k → ℂ j → ℂ k
-- -- -- -- liftDesc : ∀ {j k} → (pf : j ≤ k) → (c : ℂ j) → ℂDesc {j} c → ℂDesc {k} (liftℂ pf c)
-- -- -- -- toLift : ∀ {j k} (pf : j ≤ k) (c : ℂ j) → El c →  El (liftℂ pf c)
-- -- -- -- fromLift : ∀ {j k} (pf : j ≤ k) (c : ℂ j) →  El (liftℂ pf c) → El c
-- -- -- -- fromToLift : ∀ {j k} (pf : j ≤ k) (c : ℂ j) (x : El c) → fromLift pf c (toLift pf c x ) ≡ x
-- -- -- -- liftℂ pf CodeModule.C⁇ = C⁇
-- -- -- -- liftℂ pf CodeModule.C℧ = C℧
-- -- -- -- liftℂ pf CodeModule.C𝟘 = C𝟘
-- -- -- -- liftℂ pf CodeModule.C𝟙 = C𝟙
-- -- -- -- liftℂ (zero , pf) CodeModule.CType = transport (cong ℂ pf) CType
-- -- -- -- liftℂ (suc diff , pf) CodeModule.CType = CType {{transport (cong 0< pf) suc<}}
-- -- -- -- liftℂ pf (CodeModule.CΠ dom cod) = CΠ (liftℂ pf dom) (λ x → (liftℂ pf (cod (fromLift pf dom x))))
-- -- -- -- liftℂ pf (CodeModule.CΣ dom cod) = CΣ (liftℂ pf dom) (λ x → (liftℂ pf (cod (fromLift pf dom x))))
-- -- -- -- liftℂ pf (CodeModule.C≡ c x y) = C≡ (liftℂ pf c) (toLift pf c x) (toLift pf c y)
-- -- -- -- liftℂ pf (CodeModule.Cμ tyCtor c D x) = Cμ tyCtor (liftℂ pf c) (λ ctor → liftDesc pf c (D ctor)) (toLift pf c x)

-- -- -- -- liftDesc pf c (CodeModule.CEnd i) = CEnd (toLift pf c i)
-- -- -- -- liftDesc pf c (CodeModule.CArg c₁ D) = CArg (liftℂ pf c₁) (λ x → liftDesc pf c (D (fromLift pf c₁ x)))
-- -- -- -- liftDesc pf c (CodeModule.CRec c₁ j D) =
-- -- -- --   CRec (liftℂ pf c₁) (λ x → toLift pf c (j (fromLift pf c₁ x))) λ x → liftDesc pf c (D (fromLift pf c₁ x))

-- -- -- -- toLift pf CodeModule.C℧ x = tt
-- -- -- -- toLift pf CodeModule.C𝟘 x = x
-- -- -- -- toLift pf CodeModule.C𝟙 x = x
-- -- -- -- toLift {j = suc j} {zero} (_ , pf) CodeModule.CType x with () ← snotz (sym (+-suc _ j) ∙ pf)
-- -- -- -- toLift {j = suc j} {suc k} (diff , pf) CodeModule.CType x = liftℂ (zero , injSuc pf) x
-- -- -- -- toLift {j = suc j} {suc k} (suc diff , pf) CodeModule.CType x = liftℂ (suc diff , sym (+-suc _ j) ∙ injSuc pf) x
-- -- -- -- toLift pf (CodeModule.CΠ dom cod) f = λ x → toLift pf (cod (fromLift pf dom x)) (f (fromLift pf dom x))
-- -- -- -- toLift pf (CodeModule.CΣ dom cod) (x , y) =
-- -- -- --   toLift pf dom x , transport (cong (λ x → El (liftℂ pf (cod x))) (sym (fromToLift pf dom x))) (toLift pf (cod x) y)
-- -- -- -- toLift pf (CodeModule.C≡ c x₁ y) x = toLift pf c x
-- -- -- -- toLift pf (CodeModule.Cμ tyCtor c D x₁) x = {!!}
-- -- -- -- toLift pf CodeModule.C⁇ x = {!!}

-- -- -- -- fromLift pf CodeModule.C℧ x = tt
-- -- -- -- fromLift pf CodeModule.C𝟘 x = tt
-- -- -- -- fromLift pf CodeModule.C𝟙 x = x
-- -- -- -- fromLift (zero , pf) CodeModule.CType x = transport (sym (cong (λ x → CodeModule.ℂ-1 (CodeModuleAt x)) pf)) x
-- -- -- -- -- This is the only place we differ: can't lower the level of a type
-- -- -- -- fromLift {suc j} (suc diff , pf) CodeModule.CType x = C℧
-- -- -- -- fromLift pf (CodeModule.CΠ dom cod) f = λ x →
-- -- -- --   fromLift pf (cod x) (transport (cong (λ x → El (liftℂ pf (cod x))) (fromToLift pf dom x)) (f (toLift pf dom x)) )
-- -- -- -- fromLift pf (CodeModule.CΣ dom cod) (x , y) = fromLift pf dom x , fromLift pf (cod (fromLift pf dom x)) y
-- -- -- -- fromLift pf (CodeModule.C≡ c x₁ y) x = fromLift pf c x
-- -- -- -- fromLift pf (CodeModule.Cμ tyCtor c D x₁) x = {!!}
-- -- -- -- fromLift pf CodeModule.C⁇ x = {!!}

-- -- -- -- fromToLift pf CodeModule.C℧ x = refl
-- -- -- -- fromToLift pf CodeModule.C𝟘 x = refl
-- -- -- -- fromToLift pf CodeModule.C𝟙 x = refl
-- -- -- -- fromToLift {j = suc j} {zero} (_ , pf) CodeModule.CType x = {!!}
-- -- -- -- fromToLift {j = suc j} {suc k} (zero , pf) CodeModule.CType x = {!!}
-- -- -- -- fromToLift {j = suc j} {suc k} (suc diff , pf) CodeModule.CType x = {!!}
-- -- -- -- fromToLift pf (CodeModule.CΠ c cod) x = {!!}
-- -- -- -- fromToLift pf (CodeModule.CΣ c cod) x = {!!}
-- -- -- -- fromToLift pf (CodeModule.C≡ c x₁ y) x = {!!}
-- -- -- -- fromToLift pf (CodeModule.Cμ tyCtor c D x₁) x = {!!}
-- -- -- -- fromToLift pf CodeModule.C⁇ x = {!!}
