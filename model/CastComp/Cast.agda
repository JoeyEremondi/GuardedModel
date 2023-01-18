


-- Bound on the size of the meet on codes, assuming we have meet, cast, etc. for smaller types


open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Constructors
open import UnkGerm
open import GuardedAlgebra
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import ApproxExact
open import InductiveCodes
open import Sizes
-- open import CodePair

open import CastComp.Interface

module CastComp.Cast {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ} (cSize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed cSize )

  where

open import Code
open import Head
open import Util
open import GTypes

open import W

open SmallerCastMeet scm
open import WMuConversion

open import CastComp.ToGerm (⁇Allowed) {ℓ}
open import CastComp.FromGerm (⁇Allowed) {ℓ}
open import CastComp.CastDesc (⁇Allowed) {ℓ} cSize scm

cast : ∀ {{æ : Æ}} {h1 h2}
  → (c1 c2 : ℂ ℓ )
  → El c1
  → (view : HeadMatchView h1 h2)
  → (eq1 : h1 ≡p codeHead c1)
  → (eq2 : h2 ≡p codeHead c2)
  → (smax (codeSize c1) ( codeSize c2) ≡p cSize)
  → LÆ (El c2)

-- Casting to ℧, from ℧, or between mismatched types is an error
cast c1 c2 x (H℧L x₁) eq1 eq2 reflp = pure (℧ c2)
cast c1 c2 x (H℧R x₁) eq1 eq2 reflp = pure (℧ c2)
cast c1 c2 x (HNeq x₁) eq1 eq2 reflp = pure (℧ c2)
cast {h2 = H℧} C⁇ C℧ x (H⁇L {h2 = .H℧} reflp x₂) eq1 eq2 reflp = pure ℧𝟘
-- Casting from ⁇ to itself is the identity
cast {h2 = H⁇} C⁇ C⁇ x (H⁇L {h2 = .H⁇} reflp x₂) eq1 eq2 reflp = pure x
-- Casting from C⁇ to a type with a head
-- If the term is ⁇ or ℧, produce ⁇ or ℧ at the target type
cast {h2 = HStatic x₁} C⁇ c2 ⁇℧ (H⁇L {h2 = .(HStatic x₁)} reflp x₂) eq1 eq2 reflp = pure (℧ c2)
cast {h2 = HStatic x₁} C⁇ c2 ⁇⁇ (H⁇L {h2 = .(HStatic x₁)} reflp x₂) eq1 eq2 reflp = {!!}
-- Otherwise, check if the heads match, and if they do, extract from the germ
cast {h2 = HStatic x₁} C⁇ c2 (⁇Tag {h = h1} x) (H⁇L {h2 = (HStatic h2)} reflp x₂) eq1 eq2 reflp with headDecEq h1 h2
... | no npf = pure (℧ c2)
... | yes reflp = fromGerm _ (lowerCastMeet scm smax-≤R) c2 x (pSym eq2) reflp
-- Casting to ⁇ from a type with a head
cast c1 C⁇ x (H⁇R {h1 = h} reflp) eq1 eq2 reflp = toGerm _ (lowerCastMeet scm smax-≤L) c1 x (pSym eq1) reflp
cast C𝟙 C𝟙 x (HEq {h1 = H𝟙} reflp) eq1 eq2 reflp = pure x
cast C𝟘 C𝟘 x (HEq {h1 = H𝟘} reflp) eq1 eq2 reflp = pure x
cast Cℕ Cℕ x (HEq {h1 = Hℕ} reflp) eq1 eq2 reflp = pure x
cast CType CType x (HEq {h1 = HType} reflp) eq1 eq2 reflp = pure x
cast (CCumul x₁) (CCumul x₂) x (HEq {h1 = HCumul} reflp) eq1 eq2 reflp = {!!}
cast {{æ = æ}} (CΠ domS codS) (CΠ domD codD) f (HEq {h1 = HΠ} reflp) eq1 eq2 reflp
 = pure (λ x → fAppr x , fExact x)
    where
      fAppr : (x : El domD) → El (codD (approx  x))
      fAppr xD =
        let
          xS = ⟨ domS ⇐ domD ⟩ (approx xD) approxBy {!!}
          fxS = fst (f (exact {c = domS} xS))
          fxD = ⟨ codD (approx xD) ⇐ codS xS ⟩ (approx fxS) approxBy {!!}
        in exact fxD
      fExact : (x : El domD) → IsExact æ → LÆ (El (codD (approx  x)))
      fExact x pf = do
        xS ← ⟨ domS ⇐ domD ⟩ x By {!!}
        fxS ← snd (f xS) pf
        ⟨ codD (approx x) ⇐ codS (approx xS) ⟩ fxS By {!!}
cast (CΣ domS codS) (CΣ domD codD) (xS , yS) (HEq {h1 = HΣ} reflp) eq1 eq2 reflp = do
  xD ← ⟨ domD ⇐ domS ⟩ xS By {!!}
  yD ← ⟨ codD (approx xD) ⇐ codS (approx xS) ⟩ yS By {!!}
  pure (xD , yD)
cast (C≡ cS _ _) (C≡ cD x y) (wS ⊢ _ ≅ _)  (HEq {h1 = H≅} reflp) eq1 eq2 reflp = do
  let
    wD = ⟨ cD ⇐ cS ⟩ wS approxBy {!!}
    x⊓y = cD ∋ x ⊓ y approxBy {!!}
    wBounded = cD ∋ wD ⊓ x⊓y approxBy {!!}
  pure (wBounded ⊢ _ ≅ _)
cast (Cμ tyCtor c1 D x₁) (Cμ tyCtor2 c2 D2 x₂) x (HEq {h1 = HCtor x₃} reflp) eq1 eq2 reflp with decFin tyCtor tyCtor2
... | no _ = pure W℧
... | yes reflp = castμ D D2 x λ d →  smax-strictMono (≤ₛ-sucMono (FinLim-cocone _ _ ≤⨟ smax-≤R)) (≤ₛ-sucMono (FinLim-cocone _ _ ≤⨟ smax-≤R))



-- -------------------------------------------------------
-- -- Casting from ⁇
-- -- ---------------------------------------------------
-- --
-- --⁇ and ℧ in ⁇Ty go to ⁇ and ℧ at the target respectively
-- cast C⁇ c2 ⁇⁇ _ eq1 eq2 reflp  = {!!}
-- cast C⁇ c2 ⁇℧ _ eq1 eq2 reflp  = {!!}
-- -- Otherwise, check to see if the tags match, and cast if they do.
-- cast C⁇ c2 (⁇Tag {h = h1} x) (H⁇L {h2 = HStatic h2} reflp x₂) eq1 eq2 reflp with headDecEq h1 h2
-- ... | yes reflp = fromGerm _ (lowerCastMeet scm smax-≤R) c2 x (pSym eq2) reflp
-- -- If the heads don't match, then error
-- ... | no _ = pure (℧ c2)
-- cast {h2 = H⁇} C⁇ c2 x (H⁇L {h2 = .H⁇} reflp x₂) eq1 eq2 reflp = {!!}
-- cast {h2 = H℧} C⁇ c2 x (H⁇L {h2 = .H℧} reflp x₂) eq1 eq2 reflp = {!!}
-- -- Casting between types with the same head

-- cast {{æ = æ}} (CΠ domS codS) (CΠ domD codD) f (HEq {h1 = HΠ} reflp) eq1 eq2 reflp
--  = pure (λ x → fAppr x , fExact x)
--     where
--       fAppr : (x : El domD) → El (codD (approx  x))
--       fAppr xD =
--         let
--           xS = ⟨ domS ⇐ domD ⟩ (approx xD) approxBy {!!}
--           fxS = fst (f (approx xS))
--           fxD = ⟨ codD (approx xD) ⇐ codS xS ⟩ (approx fxS) approxBy {!!}
--         in exact fxD
--       fExact : (x : El domD) → IsExact æ → LÆ (El (codD (approx  x)))
--       fExact x pf = do
--         xS ← ⟨ domS ⇐ domD ⟩ x By {!!}
--         fxS ← snd (f xS) pf
--         ⟨ codD (approx x) ⇐ codS (approx xS) ⟩ fxS By {!!}

-- cast {{æ = æ}} (CΣ domS codS) (CΣ domD codD) (xS , yS) (HEq {h1 = HΠ} reflp) eq1 eq2 reflp = do
--   xD ← ⟨ domD ⇐ domS ⟩ xS By {!!}
--   yD ← ⟨ codD (approx xD) ⇐ codS (approx xS) ⟩ yS By {!!}
--   pure (xD , yD)
-- cast (C≡ cS _ _) (C≡ cD x y) (wS ⊢ _ ≅ _) (HEq {h1 = H≅} reflp) eq1 eq2 reflp = do
--   let
--     wD = ⟨ cD ⇐ cS ⟩ wS approxBy {!!}
--     x⊓y = cD ∋ x ⊓ y approxBy {!!}
--     wBounded = cD ∋ wD ⊓ x⊓y approxBy {!!}
--   pure (wBounded ⊢ _ ≅ _)
-- cast (CCumul x₁) (CCumul x₂) x (HEq {h1 = HCumul} reflp) eq1 eq2 reflp = {!!}
-- cast (Cμ tyCtor c1 D x₁) (Cμ tyCtor₁ c2 D₁ x₂) x (HEq {h1 = HCtor x₃} reflp) eq1 eq2 reflp = {!!}
