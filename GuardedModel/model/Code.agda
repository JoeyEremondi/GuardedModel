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
open import Cubical.Data.Equality
open import Cubical.Data.Sigma

open import Cubical.Relation.Nullary
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Inductives
open import Util
open import Cubical.Data.Maybe
open import Cubical.Data.Sum

open import ApproxExact using (Approx ; Exact ; Æ ; Approxed ; approx ; withApprox)

import GuardedAlgebra as A
import GuardedModality as G
module Code
  {{ _ : DataTypes }}
  {{ _ : DataGerms }}
  where



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
    -- El-1 : {{_ : Æ}} → ℂ-1 -> Set
    -- ⁇-1 : {{_ : Æ}} → Set
    -- ℧-1 : {{_ : 0< ℓ}} →  ℂ-1
    -- ℂSelf : ▹ Set

  interleaved mutual
    ------------------ Declarations ------------------------------
    -- Codes describing types
    data ℂ : Set
    -- Interpretation of codes into types
    El : {{æ : Æ}} → ℂ → Set
    --Approximate type for a code
    ApproxEl : ℂ → Set
    ApproxEl c = El {{Approx}} c
    -- Interpretation of codes when they're on the left of an arrow,
    -- used to make the germs of datatypes
    -- ▹El : ℂ → Set
    -- The Functor describing the unknown type ⁇
    -- We write it as a HIT to make sure all of the error values are equal
    data F⁇ {{ _ : Æ }} (Self : A.▹ Type) :  Set
    -- The unknown type, i.e. the fixed-point of F⁇
    ⁇ : {{_ : Æ}} → Set
    -- Code-based Descriptions of inductive data types
    data ℂDesc (I : ℂ) : ℂ → IndSig → Set
    -- Interpretation of description codes into descriptions
    interpDesc : ∀ {{_ : Æ}} {I} {cB} {sig} →  (ℂDesc I cB sig) → ApproxEl cB → Container (ApproxEl I)
    CommandD : ∀ {{_ : Æ}}  {I cB sig} → ℂDesc I cB sig → ApproxEl I → (ApproxEl cB → Set)
    ResponseD : ∀ {{_ :  Æ}} {I cB sig} → (D : ℂDesc I cB sig) → ∀ {i : ApproxEl I} → (b : ApproxEl cB) → CommandD D i b → Set
    inextD : ∀ {{_ : Æ}} {I cB sig} → (D : ℂDesc I cB sig) → ∀ {i} → (b : ApproxEl cB) → (c : CommandD D i b) → ResponseD D b c → ApproxEl  I
    -- ▹interpDesc : ∀{{ _ : Æ }} {I} → (ℂDesc I ) → Container 𝟙
    -- ▹CommandD : ∀ {{ _ : Æ }}{I} →  ℂDesc I  → Set
    -- ▹ResponseD : ∀ {{ _ : Æ }}{I} →  (D : ℂDesc I ) → ▹CommandD D → Set

    ------------------------------- Definitions --------------------

    ----------------------------------------------------------------
    --- Unknown type
    data _ where
      C⁇ : ℂ
      ⁇⁇ : F⁇ Self
    -- The unknown code denotes the unknown type
    El C⁇ = ⁇
    -- ▹El C⁇ = G.▹ (⁇ {{Exact}})


    ----------------------------------------------------------------
    --- Error type
    data _ where
      C℧ : ℂ
      ⁇℧ : F⁇ Self
    -- Failure is the only value of the failure type
    -- However, the code is different from C𝟘 becuase the empty type is consistent with itself
    -- But the failure type is not
    El C℧ = 𝟙
    -- ▹El C℧ = 𝟙
    ----------------------------------------------------------------
    --- Gradual empty type
    data _ where
      C𝟘 : ℂ
      -- There is no way to embed a value of the empty type into ⁇, except as error
    El C𝟘 = 𝟙
    -- ▹El C𝟘 = 𝟙
    ----------------------------------------------------------------
    --- Gradual unit type
    data _ where
      C𝟙 : ℂ
      ⁇𝟙 : F⁇ Self
    El C𝟙 = 𝟚
    -- ▹El C𝟙 = 𝟚
    ----------------------------------------------------------------
    -- Universes
    -- These are just codes from the level below
    data _ where
      CType : {{ inst : 0< ℓ }} → ℂ
      ⁇Type : {{ inst : 0< ℓ }} → ℂ-1 → F⁇ Self
    El CType = ℂ-1
    -- ▹El CType = ℂ-1
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
      -- This is where ⁇ is a non-positive type: The germ of Π is ⁇ → ⁇
      -- So we need to guard the use of ⁇ in the domain
      ⁇Π : (A.▸ Self →  (F⁇ Self )) → F⁇ Self


    El (CΠ dom cod) = (x : Approxed (El dom)) → (El (cod  (approx x)))

    ----------------------------------------------------------------
    --- Gradual pairs
    data _ where
      CΣ : (dom :  ℂ) → (cod : (x : ApproxEl dom ) → ℂ) → ℂ
      -- The germ of pairs is a pair of ⁇s
      ⁇Σ : (F⁇ Self  × F⁇ Self ) → F⁇ Self
      --TODO: is it only error if BOTH are error?
    El (CΣ dom cod) = Σ[ x ∈ Approxed (El dom) ]( El (cod (approx x)) )
    -- ▹El (CΣ dom cod) = Σ[ x ∈ ▹El dom ]( ▹El (cod (inr x)) )

    --- Gradual propositional equality i.e. witnesses of consistency
    data _ where
      C≡ : (c :  ℂ) → (x y : ApproxEl c) → ℂ
      -- The germ of an equality type is a witness of equality between two ⁇s
      ⁇≡ : _≅_ {A = F⁇ Self} ⁇⁇ ⁇⁇ → F⁇ Self
    El (C≡ c x y) = x ≅ y
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
      -- TODO: right now, must approximate taking the germ of inductives that use their parameters in dependent ways
      -- e.g. data NotProp A where np : (a b : A) → a ≠ b → NotProp A
      -- It's unclear whether we can use Induction-Induction to do this in a strictly-positive way
      ⁇μ : (tyCtor : CName) → (x : FGerm ℓ tyCtor Self (F⁇ Self)) →  F⁇ Self
    El (Cμ tyCtor cI D i) = W (Arg (λ d → interpDesc (D d) true)) 𝟙 i
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

    -- ⁇ Is the guarded fixed point of F⁇
    ⁇ = A.fix F⁇


    ----------------------------------------------------------------------
    -- Codes for descriptions of inductive types
    data ℂDesc  where
      CEnd : ∀ {cB} → (i : ApproxEl  I) → ℂDesc I cB SigE
      CArg : ∀ {cB} {rest} → (c : ApproxEl cB → ℂ) → (D : ℂDesc I (CΣ cB c) rest) → ℂDesc  I cB (SigA rest)
      CRec : ∀ {cB} {rest} (j :  ApproxEl I) → (D :  ℂDesc I cB rest) → ℂDesc I cB (SigR rest)
      CHRec : ∀ {cB} {rest} → (c : ApproxEl cB → ℂ) → (j : (b : ApproxEl cB) → ApproxEl (c b) → ApproxEl I) → (D : ℂDesc I cB rest) → ℂDesc I cB (SigHR rest)

    --adapted from https://stackoverflow.com/questions/34334773/why-do-we-need-containers
    interpDesc {I = I} {cB = cB} D b  = (λ i → CommandD D i b) ◃ ResponseD D b ◃ (λ _ → 𝟘) / inextD D b
    -- interpDesc D b  = CommandD D b  ◃ ResponseD  D  b  ◃  (λ _ → 𝟘) / inextD D b

    CommandD (CEnd j) i b = i ≅ j
    CommandD (CArg c D) i b = Σ[ a ∈ Approxed (El (c b)) ] CommandD D i (b , approx a)
    CommandD (CRec j D) i b = CommandD D i b
    CommandD (CHRec c j D) i b = CommandD D i b
--     -- CommandD (CHGuard c D E) i =  ((▹ (El c)) → CommandD D i) × CommandD E i

    ResponseD (CEnd i) b com = 𝟘
    ResponseD (CArg c D) b (a , com) = ResponseD D (b , approx a) com
    ResponseD (CRec j D) b com = Rec⇒ 𝟙    Rest⇒ (ResponseD D b com)
    ResponseD (CHRec c j D) b com = Rec⇒ (Approxed (λ {{æ}} → El {{æ}} (c b)))    Rest⇒ (ResponseD D b com)
    -- ResponseD (CHGuard c D E) (comD , comE) =
    --   GuardedArg⇒ (Σ[ a▹ ∈  ▹ El c ] (ResponseD D (comD a▹)))
    --     Rest⇒ ResponseD E comE


    inextD (CArg c D) {i} b (a , com) res = inextD D (b , approx a) com res
    inextD (CRec j D) {i} b com (Rec x) = j
    inextD (CRec j D) {i} b com (Rest x) = inextD D b com x
    inextD (CHRec c j D) {i} b com (Rec res) = j b (approx res)
    inextD (CHRec c j D) {i} b com (Rest res) = inextD D b com res
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
-----------------------------------------------------------------------




-- We can then recursively build the codes for each level
-- We take a guarded fixed-point, so we can have a code CSelf such that
-- El CSelf = ℂ
-- This gives us a version of Girard's Paradox that is safely stowed behind the guarded modality
CodeModuleAt : ∀  ℓ →  CodeModule ℓ
CodeModuleAt zero = --G.fix λ ModSelf →
  record
    { ℂ-1 = 𝟘
    -- ; El-1 = λ ()
    -- ; ⁇-1 = 𝟘
    -- ; ℧-1 = λ { {{()}} }
    -- ; ℂSelf = map▹ CodeModule.ℂ ModSelf
    }
CodeModuleAt (suc ℓ) = -- G.fix λ ModSelf →
  record
    { ℂ-1 = CodeModule.ℂ (CodeModuleAt ℓ)
    -- ; El-1 = λ x → CodeModule.El (CodeModuleAt ℓ) x
    -- ; ⁇-1 = CodeModule.⁇ (CodeModuleAt ℓ)
    -- ; ℧-1 = CodeModule.ℂ.C℧
    -- ; ℂSelf = map▹ CodeModule.ℂ ModSelf
    }

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


-- Every type has an error element
℧ : ∀ {{æ : Æ}} {ℓ} → (c : ℂ ℓ)  → El c
℧ CodeModule.C⁇ = ⁇℧
℧ CodeModule.C℧ = tt
℧ CodeModule.C𝟘 = tt
℧ CodeModule.C𝟙 = false
℧ {suc ℓ} CodeModule.CType = C℧
℧ (CodeModule.CΠ dom cod) = λ x → (℧ (cod (approx x)))
℧ (CodeModule.CΣ dom cod)  = withApprox (λ æ₁ → ℧ ⦃ æ₁ ⦄ dom) , ℧ (cod _)
-- ℧ (CodeModule.CΣ dom cod) ⦃ Exact ⦄ = (℧ dom {{Approx}} , ℧ dom {{Exact}}) , ℧ (cod (℧ dom {{Approx}})) {{Exact}}
℧ (CodeModule.C≡ c x y) = ℧ {{Approx}} c ⊢ x ≅ y
℧ (CodeModule.Cμ tyCtor c D x) = W℧

℧Approx : ∀ {ℓ} (c : ℂ ℓ) → ApproxEl c
℧Approx = ℧ {{Approx}}

℧Approxed : ∀ {{æ : Æ}} {ℓ} (c : ℂ ℓ) → Approxed (El c)
℧Approxed c = withApprox λ æ → ℧ {{æ = æ}} c


DCtors : ∀ {ℓ} → CName → ℂ ℓ → Set
DCtors tyCtor cI = (d : DName tyCtor) → ℂDesc cI C𝟙 (indSkeleton tyCtor d)


-- ⁇ : ∀ {ℓ} → (c : ℂ ℓ) → {{æ : Æ}} → El c
-- ⁇ CodeModule.C⁇ = ⁇⁇
-- ⁇ CodeModule.C℧ = tt
-- ⁇ CodeModule.C𝟘 = tt
-- ⁇ CodeModule.C𝟙 = false
-- ⁇ {suc ℓ} CodeModule.CType = C⁇
-- ⁇ (CodeModule.CΠ dom cod) = λ x → (⁇ (cod (approx x)))
-- ⁇ (CodeModule.CΣ dom cod)  = pairWithApprox (⁇ dom {{Approx}}) (⁇ dom ) , ⁇ (cod _)
-- -- ⁇ (CodeModule.CΣ dom cod) ⦃ Exact ⦄ = (⁇ dom {{Approx}} , ⁇ dom {{Exact}}) , ⁇ (cod (⁇ dom {{Approx}})) {{Exact}}
-- ⁇ (CodeModule.C≡ c x y) = ⁇⊢ x ≅ y
-- ⁇ (CodeModule.Cμ tyCtor c D x) = W⁇

-- {-# DISPLAY CodeModule.ℂ _ = ℂ  #-}
-- {-# DISPLAY CodeModule.El _  = El  #-}


▹⁇ : {{_ : Æ}} →  ℕ → A.▹ Set
▹⁇ ℓ = A.dfix (F⁇ {ℓ})

-- -- -- Lift a code to a higher universe
-- -- liftℂ : ∀ {j k} → j ≤ k → ℂ j → ℂ k
-- -- liftDesc : ∀ {j k} → (pf : j ≤ k) → (c : ℂ j) → ℂDesc {j} c → ℂDesc {k} (liftℂ pf c)
-- -- toLift : ∀ {j k} (pf : j ≤ k) (c : ℂ j) → El c →  El (liftℂ pf c)
-- -- fromLift : ∀ {j k} (pf : j ≤ k) (c : ℂ j) →  El (liftℂ pf c) → El c
-- -- fromToLift : ∀ {j k} (pf : j ≤ k) (c : ℂ j) (x : El c) → fromLift pf c (toLift pf c x ) ≡ x
-- -- liftℂ pf CodeModule.C⁇ = C⁇
-- -- liftℂ pf CodeModule.C℧ = C℧
-- -- liftℂ pf CodeModule.C𝟘 = C𝟘
-- -- liftℂ pf CodeModule.C𝟙 = C𝟙
-- -- liftℂ (zero , pf) CodeModule.CType = transport (cong ℂ pf) CType
-- -- liftℂ (suc diff , pf) CodeModule.CType = CType {{transport (cong 0< pf) suc<}}
-- -- liftℂ pf (CodeModule.CΠ dom cod) = CΠ (liftℂ pf dom) (λ x → (liftℂ pf (cod (fromLift pf dom x))))
-- -- liftℂ pf (CodeModule.CΣ dom cod) = CΣ (liftℂ pf dom) (λ x → (liftℂ pf (cod (fromLift pf dom x))))
-- -- liftℂ pf (CodeModule.C≡ c x y) = C≡ (liftℂ pf c) (toLift pf c x) (toLift pf c y)
-- -- liftℂ pf (CodeModule.Cμ tyCtor c D x) = Cμ tyCtor (liftℂ pf c) (λ ctor → liftDesc pf c (D ctor)) (toLift pf c x)

-- -- liftDesc pf c (CodeModule.CEnd i) = CEnd (toLift pf c i)
-- -- liftDesc pf c (CodeModule.CArg c₁ D) = CArg (liftℂ pf c₁) (λ x → liftDesc pf c (D (fromLift pf c₁ x)))
-- -- liftDesc pf c (CodeModule.CRec c₁ j D) =
-- --   CRec (liftℂ pf c₁) (λ x → toLift pf c (j (fromLift pf c₁ x))) λ x → liftDesc pf c (D (fromLift pf c₁ x))

-- -- toLift pf CodeModule.C℧ x = tt
-- -- toLift pf CodeModule.C𝟘 x = x
-- -- toLift pf CodeModule.C𝟙 x = x
-- -- toLift {j = suc j} {zero} (_ , pf) CodeModule.CType x with () ← snotz (sym (+-suc _ j) ∙ pf)
-- -- toLift {j = suc j} {suc k} (diff , pf) CodeModule.CType x = liftℂ (zero , injSuc pf) x
-- -- toLift {j = suc j} {suc k} (suc diff , pf) CodeModule.CType x = liftℂ (suc diff , sym (+-suc _ j) ∙ injSuc pf) x
-- -- toLift pf (CodeModule.CΠ dom cod) f = λ x → toLift pf (cod (fromLift pf dom x)) (f (fromLift pf dom x))
-- -- toLift pf (CodeModule.CΣ dom cod) (x , y) =
-- --   toLift pf dom x , transport (cong (λ x → El (liftℂ pf (cod x))) (sym (fromToLift pf dom x))) (toLift pf (cod x) y)
-- -- toLift pf (CodeModule.C≡ c x₁ y) x = toLift pf c x
-- -- toLift pf (CodeModule.Cμ tyCtor c D x₁) x = {!!}
-- -- toLift pf CodeModule.C⁇ x = {!!}

-- -- fromLift pf CodeModule.C℧ x = tt
-- -- fromLift pf CodeModule.C𝟘 x = tt
-- -- fromLift pf CodeModule.C𝟙 x = x
-- -- fromLift (zero , pf) CodeModule.CType x = transport (sym (cong (λ x → CodeModule.ℂ-1 (CodeModuleAt x)) pf)) x
-- -- -- This is the only place we differ: can't lower the level of a type
-- -- fromLift {suc j} (suc diff , pf) CodeModule.CType x = C℧
-- -- fromLift pf (CodeModule.CΠ dom cod) f = λ x →
-- --   fromLift pf (cod x) (transport (cong (λ x → El (liftℂ pf (cod x))) (fromToLift pf dom x)) (f (toLift pf dom x)) )
-- -- fromLift pf (CodeModule.CΣ dom cod) (x , y) = fromLift pf dom x , fromLift pf (cod (fromLift pf dom x)) y
-- -- fromLift pf (CodeModule.C≡ c x₁ y) x = fromLift pf c x
-- -- fromLift pf (CodeModule.Cμ tyCtor c D x₁) x = {!!}
-- -- fromLift pf CodeModule.C⁇ x = {!!}

-- -- fromToLift pf CodeModule.C℧ x = refl
-- -- fromToLift pf CodeModule.C𝟘 x = refl
-- -- fromToLift pf CodeModule.C𝟙 x = refl
-- -- fromToLift {j = suc j} {zero} (_ , pf) CodeModule.CType x = {!!}
-- -- fromToLift {j = suc j} {suc k} (zero , pf) CodeModule.CType x = {!!}
-- -- fromToLift {j = suc j} {suc k} (suc diff , pf) CodeModule.CType x = {!!}
-- -- fromToLift pf (CodeModule.CΠ c cod) x = {!!}
-- -- fromToLift pf (CodeModule.CΣ c cod) x = {!!}
-- -- fromToLift pf (CodeModule.C≡ c x₁ y) x = {!!}
-- -- fromToLift pf (CodeModule.Cμ tyCtor c D x₁) x = {!!}
-- -- fromToLift pf CodeModule.C⁇ x = {!!}
