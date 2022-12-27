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

open import Constructors

open import ApproxExact
open import W

--TODO: don't make ℓ module param
module InductiveCodes {{_ : DataTypes}} {{_ : DataGerms}} where

open import Code
-- open import Head
open import Util
open import WMuConversion

data GermCtorIsCode (ℓ : ℕ) {{æ : Æ}}  : ∀ {sig} → GermCtor sig → Type1  where
 GEndCode : GermCtorIsCode ℓ  GEnd
 GArgCode : ∀ { sig n} {A : GermTele n} {ixFor} {D : GermCtor sig}
   → (c+ : ℂ ℓ)
   → (iso+ : Iso (GermTeleEnv A) (El c+))
   → GermCtorIsCode ℓ D
   → GermCtorIsCode ℓ (GArg A ixFor D )
 GRecCode : ∀ {sig n} {A : GermTele n} {D : GermCtor sig}
   → (c+ :  ℂ ℓ)
   → (iso+ : Iso (GermTeleEnv A) (El c+))
   → GermCtorIsCode ℓ D
   → GermCtorIsCode ℓ (GRec A D)



-- open GermCtorIsCode public


-- The things we need declared for our inductive types to have them
-- fit into our Universe ala Tarski
record CodesForInductives : Type2 where
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



open CodesForInductives {{...}} public
