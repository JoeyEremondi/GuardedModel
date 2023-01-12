{-# OPTIONS --cubical --guarded #-}
open import Cubical.Data.Nat renaming (Unit to 𝟙)
open import Cubical.Data.FinData
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
open import Constructors
module Code
  {{ _ : DataTypes }}
  {{ _ : DataGerms }}
  where


open import HeadDefs


data Polarity : Set where
  Pos Neg : Polarity

data IsNeg : Polarity → Set where
  isNeg : IsNeg Neg


-- We have each level of codes and ⁇ in its own module
-- So we can then use induction afterwards to build them up from the previous level
record CodeModule
  (ℓ : ℕ)
  : Set (lsuc lzero) where
  constructor codeModule
  field
    sc : SmallerCode




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


    data HasArity : TyHead → ℕ → ℂ → Type


     -- Code-based Descriptions of inductive data types
    data ℂDesc : ℂ → IndSig → Set
    -- Interpretation of description codes into W-types
    CommandD : ∀ {{æ : Æ}}  {cB sig} → ℂDesc cB sig → (ApproxEl cB → Set)
    ResponseD : ∀ {{æ :  Æ}} {cB sig} → (D : ℂDesc cB sig) → (b : ApproxEl cB) → CommandD {{æ = Approx}} D b → Set
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
      -- However, we give it a different code from C℧, because it has different behavior
      -- with respect to consistency i.e. a computation that results in C𝟘 has *not* failed
    El C𝟘 = G𝟘
    toApprox C𝟘 x = ℧𝟘
    toExact C𝟘 x = ℧𝟘
    toApproxExact C𝟘 ℧𝟘 = refl
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


    El {{æ = Approx}} (CΠ dom cod) = (x : ApproxEl dom) →  (ApproxEl (cod x))
    El {{æ = Exact}} (CΠ dom cod) = (x : ÆEl dom Exact) → ( LÆ {{æ = Exact}} (ÆEl (cod (toApprox dom x)) Exact) × ( ApproxEl (cod (toApprox dom x))) )
    toApprox (CΠ dom cod) f x = (substPath (λ y → ÆEl (cod y) Approx) (toApproxExact dom x) ((snd (f (toExact dom x))) ))
    toExact (CΠ dom cod) f x = Now (toExact (cod (toApprox dom x)) fx) , fx
      where
        fx = (f (toApprox dom x))
    toApproxExact (CΠ dom cod) f = funExt (λ x → fromPathP (congPath f (toApproxExact dom x)))

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


    --
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

 ----------------------------------------------------------------------
    -- Codes for descriptions of inductive types
    --
    data HasArity where
      Arity0 : ∀ {h c} → HasArity h 0 c
      ArityΠ : ∀ {n} {dom : ℂ} {cod : ApproxEl dom → ℂ} → (∀ x → HasArity HΠ n (cod x)) → HasArity HΠ (ℕ.suc n) (CΠ dom cod)
      ArityΣ : ∀ {n} {dom : ℂ} {cod : ApproxEl dom → ℂ} → (∀ x → HasArity HΣ n (cod x)) → HasArity HΣ (ℕ.suc n) (CΠ dom cod)

    data ℂDesc  where
      CEnd : ∀ {cB} → ℂDesc cB SigE
      CArg : ∀ {cB n} {rest} → (c : ApproxEl cB → ℂ) → (∀ b → HasArity HΠ n (c b)) → (D : ℂDesc (CΣ cB c) rest) → (cB' : ℂ) → ((CΣ cB c) ≡p cB') → ℂDesc cB (SigA n rest)
      CRec : ∀ {cB n} {rest} → (c : ApproxEl cB → ℂ) → (∀ b → HasArity HΣ n (c b))
        → (D : ℂDesc cB rest)
        → (cB' : ℂ) → ((CΣ cB c) ≡p cB')
        → ℂDesc cB (SigR n rest)

    -- interpDesc D b  = CommandD D b  ◃ ResponseD  D  b  ◃  (λ _ → 𝟘) / inextD D b

    CommandD (CEnd) b = 𝟙
    CommandD (CArg c _ D _ _) b = Σ[ a ∈ El (c b) ] CommandD D (b , approx a)
    CommandD (CRec c _ D _ _) b = CommandD D b
--     -- CommandD (CHGuard c D E) i =  ((▹ (El c)) → CommandD D i) × CommandD E i

    ResponseD (CEnd) b com = 𝟘
    ResponseD (CArg c _ D _ _) b (a , com) = ResponseD D (b , a) com
    ResponseD (CRec c _ D _ _) b com = Rec⇒ (El (c b) )    Rest⇒ (ResponseD D b com)

    toApproxCommandD {{æ = Approx}} D b com = com
    toApproxCommandD (CEnd ) b com = com
    toApproxCommandD (CRec c _ D cB' x) b com = toApproxCommandD D b com
    toApproxCommandD (CArg c _ D cB' x) b (a , com) = approx  {c = c b}  a , toApproxCommandD D (b , approx {c = c b} a) com

    toApproxResponseD {{æ = Approx}} D b com r = r
    toApproxResponseD (CArg c _ D cB' x) b com r = toApproxResponseD D (b , (fst com)) (snd com) r
    toApproxResponseD (CRec c _  D cB' x) b com (Rec r) = Rec (approx {c = (c b)} r)
    toApproxResponseD (CRec c _  D cB' x) b com (Rest r) = Rest (toApproxResponseD D b _ r)

    toExactCommandD (CEnd ) b com = com
    toExactCommandD (CArg c _ D cB' x) b (a , com) = toExact (c b) a , toExactCommandD D (b , _) (substPath (λ a → CommandD ⦃ æ = Approx ⦄ D (b , a)) (symPath (toApproxExact (c b) a)) com)
    toExactCommandD (CRec c _  D cB' x) b com = toExactCommandD D b com

    toExactResponseD (CArg c _ D cB' x) b com r = toExactResponseD D (b , (fst com)) (snd com) r
    toExactResponseD (CRec c _ D cB' x) b com (Rec r) = Rec (toExact (c b) r)
    toExactResponseD (CRec c _ D cB' x) b com (Rest r) = Rest (toExactResponseD D b _ r)

    toApproxExactCommandD (CEnd) b com = refl
    toApproxExactCommandD (CArg c _ D cB' x) b (a , com) =
      ΣPathP
        (toApproxExact (c b) a
        , compPathEq (congP (λ _ x → toApproxCommandD ⦃ æ = Exact ⦄ D _ (toExactCommandD D _ x )) pth) (toApproxExactCommandD D _ com))
      where
        pth = symP (subst-filler (λ v → CommandD {{æ = _}} D (b , v)) (λ i₁ → toApproxExact (c b) a (~ i₁)) com)
    toApproxExactCommandD (CRec c _ D cB' x) b com = toApproxExactCommandD D b com

    toApproxExactResponseD (CArg c _ D cB' x) b com r = toApproxExactResponseD D _ (snd com) r
    toApproxExactResponseD (CRec c _ D cB' x) b com (Rec r) = congPath Rec (toApproxExact (c b) r)
    toApproxExactResponseD (CRec c _ D cB' x) b com (Rest r) = congPath Rest (toApproxExactResponseD D b com r)


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


    toApproxCommandArg : ∀ {{æ : Æ}} {cB n} {rest} → (c : ApproxEl cB → ℂ) → (arity : ∀ b → HasArity HΠ n (c b)) → (D : ℂDesc (CΣ cB c) rest) → (cB' : ℂ) → (eq : (CΣ cB c) ≡p cB')
      → (b : ApproxEl cB)
      → (a : El (c b))
      → (com : CommandD D (b , approx a))
      → toApproxCommandD (CArg c arity D cB' eq) b (a , com)  ≡c (approx a , toApproxCommandD D (b , _) com)
    toApproxCommandArg ⦃ æ = Approx ⦄ c arity D cB' peq b a com = reflc
    toApproxCommandArg ⦃ æ = Exact ⦄ c arity D cB' peq b a com = reflc

    toApproxCommandRec : ∀ {{æ : Æ}} {cB n} {rest} → (c : ApproxEl cB → ℂ) → (arity : ∀ b → HasArity HΣ n (c b)) → (D : ℂDesc cB rest) → (cB' : ℂ) → (eq : (CΣ cB c) ≡p cB')
      → (b : ApproxEl cB)
      → (com : CommandD D b)
      → toApproxCommandD (CRec c arity D cB' eq) b com  ≡c toApproxCommandD D b com
    toApproxCommandRec {{æ = Approx}} c arity D cB peq b com = reflc
    toApproxCommandRec {{æ = Exact}} c arity D cB peq b com = reflc
--     ----------------------------------------------------------------------





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

⁇CombinedTy : ∀ {{æ : Æ}} ℓ (mi : Maybe TyHead) → Set
⁇CombinedTy ℓ mi = ⁇Germ ℓ (SmallerCodeAt ℓ) (A.dfix (▹⁇Rec {ℓ = ℓ})) mi

⁇GermTy : ∀ {{æ : Æ}} ℓ (h : TyHead) → Set
⁇GermTy ℓ h = ⁇Germ ℓ (SmallerCodeAt ℓ) (A.dfix (▹⁇Rec {ℓ = ℓ})) (just h)

⁇DataGermTy : ∀ {{æ : Æ}} ℓ (tyCtor : CName) → Set
⁇DataGermTy ℓ tyCtor = ⁇Germ ℓ (SmallerCodeAt ℓ) (A.dfix (▹⁇Rec {ℓ = ℓ})) (just (HCtor tyCtor))

⁇lob : ∀ {{ æ : Æ }} {ℓ} → ⁇Ty ℓ ≡ ⁇Germ ℓ (SmallerCodeAt ℓ) (A.next (⁇Rec {ℓ = ℓ})) nothing -- F⁇ {ℓ} (A.next (⁇Rec {ℓ = ℓ}))
⁇lob {ℓ} = congPath (λ x → ⁇Germ ℓ (SmallerCodeAt ℓ) x nothing) (A.pfix (CodeModule.▹⁇Rec (CodeModuleAt ℓ))) --congPath F⁇ (A.pfix _)



unfold⁇ : ∀ {{_ : Æ}} {ℓ} → ⁇Ty ℓ →  ⁇Germ ℓ (SmallerCodeAt ℓ) (A.next (⁇Rec {ℓ = ℓ})) nothing
unfold⁇ {ℓ} x = subst (λ x → x) ⁇lob x


fold⁇ : ∀ {{_ : Æ}} {ℓ} → ⁇Germ ℓ (SmallerCodeAt ℓ) (A.next (⁇Rec {ℓ = ℓ})) nothing  → ⁇Ty ℓ
fold⁇ {ℓ} x = subst (λ x → x) (sym ⁇lob) x




-- -- Every type has an error element
-- ℧ : ∀ {{æ : Æ}} {ℓ} → (c : ℂ ℓ)  → El c
-- ℧ CodeModule.C⁇ = ⁇℧
-- ℧ CodeModule.C℧ = ℧𝟘
-- ℧ CodeModule.C𝟘 = ℧𝟘
-- ℧ CodeModule.C𝟙 = ℧𝟙
-- ℧ Cℕ = Nat℧
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


-- DCtors : ℕ → CName → Set
-- DCtors ℓ tyCtor = (d : DName tyCtor) → ℂDesc {ℓ = ℓ} C𝟙 (indSkeleton tyCtor d)


-- ▹⁇Self : {{æ : Æ}} →  ℕ → A.▹ ⁇Self
-- ▹⁇Self {{æ = æ}} ℓ = A.dfix (▹⁇Rec {ℓ = ℓ})

-- ▹⁇RecE : ∀ ℓ →  G.▹ ⁇Self → ⁇Self
-- ▹⁇RecE ℓ x = ▹⁇Rec {ℓ = ℓ} {{æ = Exact}} x




-- ▹⁇Self≡ : ∀ {{æ : Æ}} {ℓ} → ▹⁇Self ℓ ≡ A.next (⁇Rec {ℓ = ℓ})
-- ▹⁇Self≡ = A.pfix (CodeModule.▹⁇Rec (CodeModuleAt _))

-- ▹⁇ : {{æ : Æ}} →  ℕ → A.▹ Set
-- ▹⁇ ℓ = A.map▹ ⁇TySelf  (▹⁇Self ℓ)

-- ▹⁇≡ : ∀ {{æ : Æ}} {ℓ} → ▹⁇ ℓ ≡ A.next (⁇Ty ℓ)
-- ▹⁇≡ ⦃ æ = Approx ⦄ {ℓ = ℓ} = refl
-- ▹⁇≡ ⦃ æ = Exact ⦄ {ℓ = ℓ} = congPath (G.map▹ ⁇TySelf) (▹⁇Self≡ {{æ = Exact}}) ∙ G.mapNext ⁇TySelf _

-- ⁇Wrap≡ : ∀ {{æ  : Æ}} {ℓ} → A.▸ (▹⁇ ℓ) ≡c (A.▹ (⁇Ty ℓ))
-- ⁇Wrap≡ {{æ = Exact}} = G.later-extSwap (λ α → pfixSelf' α)
--   where
--     pfixSelf' : ∀ {ℓ} →  G.▸ \ α → ( ⁇TySelf (G.dfix (▹⁇RecE ℓ) α) ≡ ⁇TySelf (▹⁇RecE ℓ (G.dfix (▹⁇RecE ℓ))))
--     pfixSelf' tic = cong ⁇TySelf (G.pfix' (▹⁇RecE _) tic)
-- ⁇Wrap≡ {{æ = Approx}} = reflc

-- apply⁇Fun : ∀ {{æ : Æ}} {ℓ} → (▹⁇Ty (▹⁇Self ℓ) → ⁇Ty ℓ) → ⁇Ty ℓ → ⁇Ty ℓ
-- apply⁇Fun {ℓ = ℓ} f x =
--   f (transport (symPath ⁇Wrap≡) (A.next x))
