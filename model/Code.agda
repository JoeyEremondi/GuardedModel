{-# OPTIONS --cubical --guarded #-}
-- open import Desc
-- open import Level hiding (#_)
open import Cubical.Data.Nat renaming (Unit to 𝟙)
open import Cubical.Data.FinData
-- open import Cubical.Data.Bool renaming (Bool to 𝟚)
open import Cubical.Data.Empty renaming (⊥ to 𝟘)
open import Cubical.Data.Nat.Order
open import Cubical.HITs.SetQuotients
open import DecPEq
open import Cubical.Data.Sigma

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Bool
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import UnkGerm
open import Cubical.Data.Sum as Sum
open import W
open import Util
open import Cubical.Data.Maybe
open import Cubical.Data.Sum

open import ApproxExact

open import GTypes

import GuardedAlgebra as A
import GuardedModality as G
module Code
  {{ _ : DataTypes }}
  {{ _ : DataGerms }}
  where


open import HeadDefs (numTypes)


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




  -- Take the fixed point to get the actual type
  ▹⁇Rec : {{æ : Æ}} → A.▹ ⁇Self → ⁇Self
  ▹⁇Rec Self = record { ⁇TySelf = ⁇Germ ℓ sc Self nothing ; ⁇⁇Self = ⁇⁇ ; ⁇℧Self = ⁇℧ }
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


    record ℂCtor : Type
    interpCtor : {{æ : Æ}} → (tyCtor : CName) → DName tyCtor → ℂCtor → Container 𝟙


    toApproxμ :
      (tyCtor : CName)
        → (D : (d : DName tyCtor) → ℂCtor)
        → W̃ (Arg (λ d → interpCtor {{æ = Exact}} tyCtor d (D d) )) tt
        → W̃ (Arg (λ d → interpCtor {{æ = Approx}} tyCtor d (D d) )) tt
    toExactμ :
      (tyCtor : CName)
        → (D : (d : DName tyCtor) → ℂCtor)
        → W̃ (Arg (λ d → interpCtor {{æ = Approx}} tyCtor d (D d) )) tt
        → W̃ (Arg (λ d → interpCtor {{æ = Exact}} tyCtor d (D d) )) tt
    toApproxExactμ :
        (tyCtor : CName)
          → (D : (d : DName tyCtor) → ℂCtor)
          → (x : W̃ (Arg (λ d → interpCtor {{æ = Approx}} tyCtor d (D d) ) ) tt)
          → toApproxμ tyCtor D (toExactμ tyCtor D x) ≡c x


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

    -- Natural numbers
    -- We could have these as inductives, but we really just need them for a hack in our ordinals
    data _ where
      Cℕ : ℂ
    El Cℕ = GNat
    toApprox Cℕ n = n
    toExact Cℕ n = n
    toApproxExact Cℕ n = reflc

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
        →  (D : (d : DName tyCtor) → ℂCtor) -- (D : (d : DName tyCtor) → ℂDesc C𝟙 (indSkeleton tyCtor d))
        → ApproxEl cI
        → ℂ
    El (Cμ tyCtor cI D i) =  W̃ (Arg (λ d → interpCtor tyCtor d (D d))) tt
    -- toApprox (Cμ tyCtor cI Ds iStart) (Wsup (FC (d , com) res)) =
    --   with (FC retCom retRes) ← toApproxDesc {Y = λ j → {!!}} (Ds d) true {!!} (FC com res) (λ r → {!!})
    --   = {!x!}
    -- toApprox (Cμ tyCtor cI Ds iStart) W⁇ = W⁇
    -- toApprox (Cμ tyCtor cI Ds iStart) W℧ = W℧
    toApprox (Cμ tyCtor cI Ds iStart) x = toApproxμ tyCtor Ds x -- toApproxμ tyCtor C𝟙 Ds Gtt x
    toExact (Cμ tyCtor cI Ds iStart) x =  toExactμ tyCtor Ds x -- toExactμ tyCtor C𝟙 Ds Gtt x
    toApproxExact (Cμ tyCtor cI Ds i) x = toApproxExactμ tyCtor Ds x -- toApproxExactμ tyCtor C𝟙 Ds Gtt x


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
    -- TODO update description
    record ℂCtor where
      constructor CCtor
      inductive
      field
        ℂCommand : ℂ
        ℂHOResponse : ApproxEl ℂCommand → ℂ
    open ℂCtor public

    interpCtor tyCtor d ctor = (λ _ → El (ℂCommand ctor)) ◃ (λ c →  Fin (#FO tyCtor d) ⊎ El (ℂHOResponse ctor (approx c))) / (λ _ _ → tt)


    -- WPathP :
    --       ∀ {{æ : Æ}}  {tyCtor : CName}
    --         → { Ds : (d : DName tyCtor) → ℂCtor}
    --         → { d : DName tyCtor }
    --         → {com1 com2 : El (ℂCommand (Ds d))}
    --         → {res1 : (r : ?) → W̃ (Arg (λ d → interpDesc (Ds d) b)) tt }
    --         → {res2 : (r : ?) → W̃ (Arg (λ d → interpDesc (Ds d) b)) tt }
    --         → (eqc : com1 ≡c com2)
    --         → (eqr :
    --               ∀ ( x₀ : ? )
    --               ( x₁ :  ?)
    --               (p
    --               : PathP
    --                 (λ z → ?) →
    --               PathP (λ i₁ →
    --                 W̃ (Arg (λ d₁ → interpDesc (Ds d₁) b))
    --                 (inext (interpDesc (Ds d) b) (eqc i₁) (p i₁)))
    --               (res1 x₀) (res2 x₁)
    --           )
    --         → _≡c_ {A = W̃ (Arg (λ d → interpDesc (Ds d) b)) tt }
    --           (Wsup (FC (d , com1) res1 ))
    --           (Wsup (FC (d , com2) res2 ))
    -- WPathP {Ds = Ds} {b = b} {d = d} {com1 = com1} {com2 = com2} {res1 = res1} {res2 = res2}
    --       eqc eqr =
    --         cong₂ {B = λ c → (r : ResponseD {{æ = _}} (Ds d) b (toApproxCommandD (Ds d) b c)) → _}
    --           {x = com1} {y = com2}
    --           (λ c r → Wsup (FC (d , c) r) )
    --           eqc
    --           {u = res1} {v = res2}
    --           (funExtDep (λ {x} {x1} pth → eqr x x1 pth))

    toApproxμ _ _ W⁇ = W⁇
    toApproxμ _ _ W℧ = W℧
    toApproxμ tyCtor Ds (Wsup (FC (d , com) resp)) = Wsup (FC (d , toApprox (ℂCommand (Ds d)) com)
      (Sum.elim (λ n → toApproxμ tyCtor Ds (resp (inl n)))
                λ r → toApproxμ tyCtor Ds (resp (inr (toExact (ℂHOResponse (Ds d) (toApprox _ com)) r)))))

    toExactμ _ _ W⁇ = W⁇
    toExactμ _ _ W℧ = W℧
    toExactμ tyCtor Ds (Wsup (FC (d , com) resp)) = Wsup (FC (d , toExact (ℂCommand (Ds d)) com)
      (Sum.elim (λ n → toExactμ tyCtor Ds (resp (inl n)))
                λ r → toExactμ tyCtor Ds (resp (inr (substPath (λ x → El {{æ = Approx}} (ℂHOResponse (Ds d) x)) (toApproxExact _ com) (toApprox _ r))))))

    toApproxExactμ _ _ W⁇ = reflc
    toApproxExactμ _ _ W℧ = reflc
    toApproxExactμ tyCtor Ds (Wsup (FC (d , com) resp)) =
      cong₂
        {A = Command (interpCtor ⦃ æ = Approx ⦄ tyCtor d (Ds d)) tt}
        {B = λ c → (r : Response (interpCtor {{æ = _}} tyCtor d (Ds d)) c) → W̃ (Arg (λ d → interpCtor {{æ = _}} tyCtor d (Ds d)) ) tt}
        {x = toApprox (ℂCommand (Ds d)) (toExact (ℂCommand (Ds d)) com)} {y = com}
        {C = λ com res → W̃ ((λ i →
                                Σ _
                                (λ a → El {{æ = _}} (ℂCommand (Ds a))))
                             ◃ Response (Arg (λ d₁ → interpCtor {{æ = _}} tyCtor d₁ (Ds d₁))) /
                             (λ {i} c _ → tt)) tt }
        (λ c r → Wsup (FC (d , c) r))
        (toApproxExact (ℂCommand (Ds d)) com)
        (funExtDep λ { {x0} {x1} pth → helper x0 x1 pth ∙ sym (respη x1) }) -- (funExtDep (λ { {x0} {x1} pth → helper x0 x1 pth (ptoc pth)}))
      where
        respη : ∀ x → resp x ≡c Sum.elim {C = λ r → W̃ _ tt} (λ r → resp (inl r)) (λ r → resp (inr r)) x
        respη (inl x) = reflc
        respη (inr x) = reflc
        sumPath : ∀ {X Y X' Y' C : Type} {f1 : X → C} {f2 : Y → C} {f1' : X' → C} {f2' : Y' → C} {x : X ⊎ Y} {x' : X' ⊎ Y'}
          → (px : X ≡c X') → (py : Y ≡c Y')
          → PathP (λ i → px i → C) f1 f1'
          → PathP (λ i → py i → C) f2 f2'
          → PathP (λ i → px i  ⊎ py i) x x'
          → Sum.elim {A = X} {B = Y} {C = λ _ → C } f1 f2 x ≡c Sum.elim {A = X'} {B = Y'} f1' f2' x'
        sumPath px py pf1 pf2 parg  i = Sum.elim (pf1 i) (pf2 i) (parg i)
        helper : (x0 : _) → (x1 : _) → _ → _
        helper x0 x1 pth = sumPath reflc (congPath (λ x → El {{æ = Approx}} (ℂHOResponse (Ds d) x)) (toApproxExact _ com))
          (funExt (λ r → toApproxExactμ tyCtor Ds (resp (inl r))))
          (funExtDep (λ {r0} {r1} rpth → toApproxExactμ tyCtor Ds _ ∙ congPath (λ r → resp (inr r)) (fromPathP {A = λ i → El ⦃ æ = Approx ⦄ (ℂHOResponse (Ds d) (toApproxExact _ com i))}
          (λ i → toApproxExact _ (rpth i) i))))
          pth
        -- helper (inl x) (inl x₁) pth = ? -- toApproxExactμ tyCtor (λ d₁ → Ds d₁) (resp (inl x))
        -- --sym (toApproxExactμ tyCtor Ds (resp (inl x)))
        -- helper (inr x) (inr x₁) pth = toApproxExactμ tyCtor Ds (resp
        --                                                                (inr
        --                                                                 (toApprox (ℂHOResponse (Ds d) {!!}) (toExact (ℂHOResponse (Ds d) {!!}) x)))) ∙ congPath (λ x → resp (inr x)) (toApproxExact (ℂHOResponse (Ds d) {!!}) x)


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

⁇Ty : ∀ {{æ : Æ}} ℓ → Set
⁇Ty {{æ}} ℓ = (CodeModule.⁇ (CodeModuleAt ℓ) {{æ}})

⁇GermTy : ∀ {{æ : Æ}} ℓ (tyCtor : CName) → Set
⁇GermTy ℓ tyCtor = ⁇Germ ℓ (SmallerCodeAt ℓ) (A.dfix (▹⁇Rec {ℓ = ℓ})) (just tyCtor)

⁇lob : ∀ {{ æ : Æ }} {ℓ} → ⁇Ty ℓ ≡ ⁇Germ ℓ (SmallerCodeAt ℓ) (A.next (⁇Rec {ℓ = ℓ})) nothing -- F⁇ {ℓ} (A.next (⁇Rec {ℓ = ℓ}))
⁇lob {ℓ} = congPath (λ x → ⁇Germ ℓ (SmallerCodeAt ℓ) x nothing) (A.pfix (CodeModule.▹⁇Rec (CodeModuleAt ℓ))) --congPath F⁇ (A.pfix _)



unfold⁇ : ∀ {{_ : Æ}} {ℓ} → ⁇Ty ℓ →  ⁇Germ ℓ (SmallerCodeAt ℓ) (A.next (⁇Rec {ℓ = ℓ})) nothing
unfold⁇ {ℓ} x = subst (λ x → x) ⁇lob x


fold⁇ : ∀ {{_ : Æ}} {ℓ} → ⁇Germ ℓ (SmallerCodeAt ℓ) (A.next (⁇Rec {ℓ = ℓ})) nothing  → ⁇Ty ℓ
fold⁇ {ℓ} x = subst (λ x → x) (sym ⁇lob) x




-- Every type has an error element
℧ : ∀ {{æ : Æ}} {ℓ} → (c : ℂ ℓ)  → El c
℧ CodeModule.C⁇ = ⁇℧
℧ CodeModule.C℧ = ℧𝟘
℧ CodeModule.C𝟘 = tt
℧ CodeModule.C𝟙 = ℧𝟙
℧ Cℕ = Nat℧
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


DCtors : (ℓ : ℕ) → CName → Set
DCtors ℓ tyCtor = (d : DName tyCtor) → ℂCtor {ℓ = ℓ}


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
