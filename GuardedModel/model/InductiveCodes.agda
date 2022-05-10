{-# OPTIONS --cubical --guarded #-}



-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary

open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq hiding (_∎)
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (⊥ to 𝟘)
-- open import Cubical.Data.Prod
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Inductives
open import GuardedAlgebra
import GuardedModality as G
open import Cubical.Induction.WellFounded
open import Cubical.Foundations.Prelude
open import Cubical.Data.Equality using (ptoc ; ctop)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Sum
open import GuardedModality using (later-ext)

open import ApproxExact


--TODO: don't make ℓ module param
module InductiveCodes {{_ : DataTypes}} {{_ : DataGerms}} where

open import Code
-- open import Head
open import Util

open import Ord -- ℂ El ℧ C𝟙 refl
-- open import InductiveCodes

-- interpGermUnk : GermDesc → ℕ → Container Unit
-- GermUnkCommand : GermDesc → ℕ → Set
-- GermUnkCommand GEnd ℓ = Unit
-- GermUnkCommand (GArg A D) ℓ = Σ[ x ∈ A ] GermUnkCommand (D x) ℓ
-- GermUnkCommand (GHRec A D) ℓ = (a : A) → GermUnkCommand (D a) ℓ
-- GermUnkCommand (GUnk A D) ℓ = (A → ⁇Ty ℓ) × GermUnkCommand D ℓ

-- GermUnkResponse : (D : GermDesc) → (ℓ : ℕ) → GermUnkCommand D ℓ → Set
-- GermUnkResponse GEnd ℓ _ = 𝟘
-- GermUnkResponse (GArg A D) ℓ (a , com) = GermUnkResponse (D a) ℓ com
-- GermUnkResponse (GHRec A D) ℓ com = Rec⇒ A  Rest⇒ (Σ[ a ∈ A ] GermUnkResponse (D a) ℓ (com a))
-- GermUnkResponse (GUnk A D) ℓ (f , com) = Rec⇒ ⁇Ty ℓ  Rest⇒ (A → ⁇Ty ℓ) × GermUnkResponse D ℓ com

-- Like El, but interprets C⁇ to ▹⁇


-- Predicate for when a type is the interpretation of some code, modulo guardedness
data IsGuardedCode (ℓ : ℕ) {{æ : Æ}} : Set → Set1
data DataGermIsCode (ℓ : ℕ) {{æ : Æ}}  : {B : Set} → GermCtor B → Set1

data IsGuardedCode ℓ where
  IsGRefl : ∀ {A c} → Iso A (El {ℓ} c) → IsGuardedCode ℓ A
  IsGGuarded : ∀ {A} → IsGuardedCode ℓ A → IsGuardedCode ℓ (▹ A)
  IsGReflG : ∀ {c} → IsGuardedCode ℓ (▹ (El {ℓ} c))
  IsGΠ  : ∀ {Dom} {Cod : Dom → Set} → IsGuardedCode ℓ Dom → (∀ x → IsGuardedCode ℓ (Cod x)) → IsGuardedCode ℓ ((x : Dom) → Cod x)
  IsGΣ : ∀ {Dom} {Cod : Dom → Set} → IsGuardedCode ℓ Dom → (∀ x → IsGuardedCode ℓ (Cod x)) → IsGuardedCode ℓ (Σ[ x ∈ Dom ]( Cod x ))
  IsG≡ : ∀ {A} {x y : A} → IsGuardedCode ℓ A → IsGuardedCode ℓ (x ≅ y)
  -- Data germs can only contain descriptions from other germs, so all inductives are coded with GermCtors
  -- TODO: is this right?
  IsGμ : ∀ (tyCtor : CName) (D : DName tyCtor → GermCtor Unit)  → (∀ d → DataGermIsCode ℓ (D d)) → IsGuardedCode ℓ (FGerm ℓ tyCtor (▹⁇ ℓ) (⁇Ty ℓ))

-- Predicate classifying whether a datagerm description is equivalent to a ℂDesc
--TODO: do we still need this with the more strict code requirements?

data DataGermIsCode ℓ where
 GEndCode : ∀ {B} → DataGermIsCode ℓ {B} GEnd
 GRecCode : ∀ {B} {D : GermCtor B}
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GRec D)
 GArgCode : ∀ {B} {A : B → Set} {D : GermCtor (Σ B A)} → (∀ b → IsGuardedCode ℓ (A b))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GArg A D)
 GHRecCode : ∀ {B} {A : B → Set} {D : GermCtor B} → (∀ b → IsGuardedCode ℓ (A b))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GHRec A D)
 GUnkCode : ∀ {B} {A : B → Set} {D : GermCtor B} (c : B → ℂ ℓ) → (∀ b → IsGuardedCode ℓ (A b))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GUnk A D)



record InductiveCodes : Set2 where
  field
    ℓₚ : (ℓ : ℕ) → CName → ℕ
    Params : (ℓ : ℕ) → (tyCtor : CName) → ℂ (ℓₚ ℓ tyCtor)
    Indices : (ℓ : ℕ) → (tyCtor : CName) → ApproxEl (Params ℓ tyCtor) → ℂ ℓ
    descFor : (ℓ : ℕ) → (tyCtor : CName)
      → (pars : ApproxEl (Params ℓ tyCtor))
      → (d : DName tyCtor)
      → ℂDesc (Indices ℓ tyCtor pars) C𝟙
    --Every data germ can be described by a code, with some parts hidden behind the guarded modality
    dataGermIsCode : ∀ {{_ : Æ}} (ℓ : ℕ) (tyCtor : CName) (d : DName tyCtor)
      → DataGermIsCode ℓ (dataGerm ℓ tyCtor (▹⁇ ℓ) d)

  -- Predicate that determines if a code is well formed
  -- with respect to the inductive types it refers to
  -- i.e. if it's an instantation of that type's parameters and indices
  data IndWF {ℓ} : ℂ ℓ → Prop where
   IWF⁇ : IndWF C⁇
   IWF℧ : IndWF C℧
   IWF𝟘 : IndWF C𝟘
   IWF𝟙 : IndWF C𝟙
   IWFType : ∀ {{_ : 0< ℓ}} → IndWF CType
   IWFΠ : ∀ {dom cod}
     → IndWF dom
     → (∀ x → IndWF (cod x))
     → IndWF (CΠ dom cod)
   IWFΣ : ∀ {dom cod}
     → IndWF dom
     → (∀ x → IndWF (cod x))
     → IndWF (CΣ dom cod)
   IWF≡ : ∀ {c x y} → IndWF c → IndWF (C≡ c x y)
   IWFμ : ∀ {tyCtor cI D i}
     → (pars : ApproxEl (Params ℓ tyCtor))
     → (indEq : cI ≡ Indices ℓ tyCtor pars)
     → (∀ d → PathP (λ i → ℂDesc (indEq i) C𝟙) (D d) (descFor ℓ tyCtor pars d))
     → IndWF (Cμ tyCtor cI D i)


open InductiveCodes {{...}} public
