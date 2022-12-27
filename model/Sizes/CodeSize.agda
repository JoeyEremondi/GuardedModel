

{-# OPTIONS --cubical --guarded -v term:50 #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
-- open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat as Nat
import Cubical.Data.Nat.Order as Nat
import Cubical.Induction.WellFounded as Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool
-- open import Cubical.Data.Equality
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import UnkGerm
open import GuardedAlgebra
import GuardedModality as G
open import Cubical.Induction.WellFounded
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import InductiveCodes
open import W
-- open import Cubical.Data.Equality using (ptoc)

open import ApproxExact
open import GTypes
open import Sizes.NatLim


-- open import InductiveCodes
open import Cubical.Foundations.Transport


-- Brouwer Tree ordinals
-- Based on the presentation by Kraus, Forsburg and Xu
-- https://arxiv.org/abs/2104.02549

-- The main difference is that we allow the limit over the elements of any code type, not just natural numbers

open import Code

open import Sizes.MultiMax

open import InductiveCodes
open import Head
open import Util
open import Constructors

open import Sizes.Size -- ℂ El ℧ C𝟙 refl
module Sizes.CodeSize {{_ : DataTypes}} {{_ : DataGerms}} {{_ : CodesForInductives }}
    (ℓ : ℕ)
    (smallerCodeSize : {{inst : 0< ℓ}} → ℂ-1 (SmallerCodeAt ℓ ) → Size)
    -- (smallerElSize : {{æ : Æ }} → {{inst : 0< ℓ}} → (c : ℂ-1 (SmallerCodeAt ℓ)) → El-1 (SmallerCodeAt ℓ) c → Size)
  where







codeSize' : ℂ ℓ → Size
descSize' : ∀ {cB : ℂ ℓ} { sig} → ℂDesc cB sig → Size

-- The unknown type has a size that is larger than all other sizes
-- We hack this using limits of ordinals
-- TODO will this actually work?
codeSize' C⁇ = S1
codeSize' C℧ = S1
codeSize' C𝟘 = S1
codeSize' C𝟙 = S1
codeSize' Cℕ = S1
codeSize' CType = S1
codeSize' (CΠ dom cod) =
  S↑ (smax
    ( (codeSize' dom))
    ( (SLim dom λ x →  (codeSize' (cod x)))))
codeSize' (CΣ dom cod) =
  S↑ (smax
    ( (codeSize' dom))
    (  (SLim dom λ x →  (codeSize' (cod x)))))
codeSize'  (C≡ c x y) = S↑ ( (codeSize' c))
codeSize' (Cμ tyCtor c D x) = S↑ (DLim tyCtor λ d → descSize' (D d))
codeSize' (CCumul x) = smallerCodeSize x

descSize' CEnd = S1
descSize' (CArg c hasArity D cB' reflp) = S↑ (smax (SLim _ λ b → codeSize' (c b)) (descSize' D))
descSize' (CRec c hasArity D cB' reflp) = S↑ (smax (SLim _ λ b → codeSize' (c b)) (descSize' D))
