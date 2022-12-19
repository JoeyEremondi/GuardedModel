{-# OPTIONS --cubical --guarded #-}



-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary

open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (⊥ to 𝟘)
open import Cubical.Data.Unit renaming (Unit to 𝟙)
-- open import Cubical.Data.Prod
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import UnkGerm
open import GuardedAlgebra
import GuardedModality as G
open import Cubical.Induction.WellFounded
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Sum
open import GuardedModality using (later-ext)

open import ApproxExact
open import W

--TODO: don't make ℓ module param
module InductiveCodes {{_ : DataTypes}} {{_ : DataGerms}} where

open import Code
-- open import Head
open import Util

open import Ord -- ℂ El ℧ C𝟙 refl

-- Predicate for a Germ Constructor whose types are all given by codes in our universe
record GermCtorIsCode {{æ : Æ}} (ℓ : ℕ) (ctor : GermCtor) : Type1 where
  inductive
  field
    germCommandCode : ℂ ℓ
    germCommandIso : Iso (GermCommand ctor) (El germCommandCode)
    germHOCode : El germCommandCode → ℂ ℓ
    germHOIso : ∀ com → Iso (GermHOResponse ctor com) (El (germHOCode (Iso.fun germCommandIso com)))
    germHOUnkCode : El germCommandCode → ℂ ℓ
    germHOUnkIso : ∀ com → Iso (GermHOUnkResponse ctor com) (El (germHOCode (Iso.fun germCommandIso com)))

-- Inductive representation of W-types, again useful for convincing Agda things terminate
record ℂFunctor {{æ  : Æ}} ℓ (tyCtor : CName) (ctors : DCtors ℓ tyCtor) (X : Type) :  Type where
  inductive
  constructor ℂEl
  field
    d : DName tyCtor
    com : El (ℂCommand (ctors d))
    foResp : Fin (#FO tyCtor d) → X
    hoResp : (r : El (ℂHOResponse (ctors d) (approx com))) → X

data ℂμ {{æ  : Æ}} ℓ (tyCtor : CName) (ctors : DCtors ℓ tyCtor) : Type where
  ℂinit : ℂFunctor ℓ tyCtor ctors (ℂμ ℓ tyCtor ctors) → ℂμ ℓ tyCtor ctors
  μ⁇ μ℧ : ℂμ ℓ tyCtor ctors

-- The things we need declared for our inductive types to have them
-- fit into our Universe ala Tarski
record CodesForInductives : Set2 where
  field
    ℓₚ : (ℓ : ℕ) → CName → ℕ
    Params : (ℓ : ℕ) → (tyCtor : CName) → ℂ (ℓₚ ℓ tyCtor)
    Indices : (ℓ : ℕ) → (tyCtor : CName) → ApproxEl (Params ℓ tyCtor) → ℂ ℓ
    descFor : (ℓ : ℕ) → (tyCtor : CName)
      → (pars : ApproxEl (Params ℓ tyCtor))
      → (indices : ApproxEl (Indices ℓ tyCtor pars))
      → (DCtors ℓ tyCtor )
  DataGermIsCode : Type1
  DataGermIsCode =  ∀ {{_ : Æ}} (ℓ : ℕ) (tyCtor : CName) (d : DName tyCtor)
      → GermCtorIsCode ℓ (germCtor ℓ tyCtor d)

  field
    --Every data germ can be described by a code, with some parts hidden behind the guarded modality
    dataGermIsCode : DataGermIsCode

  -- Inductive type for codes that includes the codes for germs as fields
  -- This is awkward, but needed to convince Agda that our size calculation halts
  data CodeSizer {ℓ} : ℂ ℓ → Type1
  data CtorSizer {ℓ} : (ℂCtor {ℓ = ℓ}) → Type1
  data CodeSizer {ℓ} where
    -- We need to
    CS⁇ : (dgIsCode : ∀ {{æ : Æ}} → _) → (∀ {{æ : Æ}} → dgIsCode ≡c dataGermIsCode) → CodeSizer C⁇
    CS℧ : CodeSizer C℧
    CS𝟘 : CodeSizer C𝟘
    CS𝟙 : CodeSizer C𝟙
    CSType : ∀ {{inst : 0< ℓ}} → CodeSizer CType
    CSCumul : ∀ {{inst : 0< ℓ}} {c} → CodeSizer (CCumul c)
    CSΠ : ∀ {dom cod} → CodeSizer dom → (∀ x → CodeSizer (cod x)) → CodeSizer (CΠ dom cod)
    CSΣ : ∀ {dom cod} → CodeSizer dom → (∀ x → CodeSizer (cod x)) → CodeSizer (CΣ dom cod)
    CS≡ : ∀ {c x y} → CodeSizer c → CodeSizer (C≡ c x y)
    CSμ : ∀ {tyCtor cI D i}
      → (∀ d → CtorSizer (D d))
      → CodeSizer (Cμ tyCtor cI D i)
  data CtorSizer {ℓ} where
    CElS :
      ∀ {c r}
      → CodeSizer c
      → (∀ x → CodeSizer (r x))
      → CtorSizer (record { ℂCommand = c ; ℂHOResponse = r })

  codeSizer : ∀ {ℓ} (c : ℂ ℓ ) → CodeSizer c
  ctorSizer : ∀ {ℓ} (c : ℂCtor {ℓ = ℓ}) → CtorSizer c
  codeSizer C⁇ = CS⁇ _ reflc
  codeSizer C℧ = CS℧
  codeSizer C𝟘 = CS𝟘
  codeSizer C𝟙 = CS𝟙
  codeSizer CType = CSType
  codeSizer (CCumul x) = CSCumul
  codeSizer (CΠ c cod) = CSΠ (codeSizer c) (λ x → codeSizer _)
  codeSizer (CΣ c cod) = CSΣ (codeSizer c) (λ x → codeSizer _)
  codeSizer (C≡ c x y) = CS≡ (codeSizer _) 
  codeSizer (Cμ tyCtor c D x) = CSμ (λ d → ctorSizer _)
  ctorSizer D = CElS (codeSizer _) (λ x → codeSizer _)

  -- Every Inductive type can be converted to a ℂμ
  toℂμ : ∀ {{æ  : Æ}} ℓ (tyCtor : CName) (ctors : DCtors ℓ tyCtor) →
    W̃ (Arg (λ d → interpCtor tyCtor d (ctors d))) tt → ℂμ ℓ tyCtor ctors
  toℂμ ℓ tyCtor ctors W℧ = μ℧
  toℂμ ℓ tyCtor ctors W⁇ = μ⁇
  toℂμ ℓ tyCtor ctors (Wsup (FC (d , com) resp)) = ℂinit (toℂFunctor d (ℂμ ℓ tyCtor ctors) (FC com λ r → toℂμ ℓ tyCtor ctors (resp r)))
    where
        toℂFunctor : ∀ (d : DName tyCtor) (X : Type) →
            ⟦ interpCtor tyCtor d  (ctors d) ⟧F (λ _ → X) tt → ℂFunctor ℓ tyCtor ctors X
        toℂFunctor d X (FC com resp) = ℂEl d com (λ r → resp (inl r)) λ r → resp (inr r)

open CodesForInductives {{...}} public
