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


-- Predicate classifying whether a datagerm description is equivalent to a ℂDesc
--TODO: do we still need this with the more strict code requirements?
data DataGermIsCode (ℓ : ℕ) {{æ : Æ}}  : {B : Set} → GermCtor B → Set2  where
 GEndCode : ∀ {B} → DataGermIsCode ℓ {B} GEnd
 GRecCode : ∀ {B} {D : GermCtor B} (c : B → ℂ ℓ)
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GRec D)
 GArgCode : ∀ {B} {A : B → Set} {D : GermCtor (Σ B A)} (c : B → ℂ ℓ) → (∀ b → Iso (A b) (El (c b)))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GArg A D)
 GHRecCode : ∀ {B} {A : B → Set} {D : GermCtor B} (c : B → ℂ ℓ) → (∀ b → Iso (A b) (El (c b)))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GHRec A D)
 GUnkCode : ∀ {B} {A : B → Set} {D : GermCtor B} (c : B → ℂ ℓ) → (∀ b → Iso (A b) (El (c b)))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GUnk A D)
 GGuardedArgCode : ∀ {B} {A : B → Set} {D : GermCtor (Σ B A)} (c : B → ℂ ℓ) → (∀ b → Iso (A b) (G.▹ (El (c b))))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GArg A D)
 GGuardedHRecCode : ∀ {B} {A : B → Set} {D : GermCtor B} (c : B → ℂ ℓ) → (∀ b → Iso (A b) (G.▹ El (c b)))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GHRec A D)
 GGuardedUnkCode : ∀ {B} {A : B → Set} {D : GermCtor B} (c : B → ℂ ℓ) → (∀ b → Iso (A b) (G.▹ El (c b)))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GUnk A D)




record InductiveCodes : Set2 where
  field
    ℓₚ : (ℓ : ℕ) → CName → ℕ
    Params : (ℓ : ℕ) → (tyCtor : CName) → ℂ (ℓₚ ℓ tyCtor)
    Indices : (ℓ : ℕ) → (tyCtor : CName) → ApproxEl (Params ℓ tyCtor) → ℂ ℓ
    descFor : (ℓ : ℕ) → (tyCtor : CName)
      → (pars : ApproxEl (Params ℓ tyCtor))
      → (DCtors tyCtor (Indices ℓ tyCtor pars))
    --Every data germ can be described by a code, with some parts hidden behind the guarded modality
    dataGermIsCode : ∀ {{_ : Æ}} (ℓ : ℕ) (tyCtor : CName) (d : DName tyCtor)
      → DataGermIsCode ℓ (dataGerm ℓ tyCtor (▹⁇ ℓ) d)

  -- Predicate that determines if a code is well formed
  -- with respect to the inductive types it refers to
  -- i.e. if it's an instantation of that type's parameters and indices
  interleaved mutual
    data IndWF {ℓ} : ℂ ℓ → Set
    -- data DescIndWF {ℓ} {cI cB : ℂ ℓ } : ℂDesc cI cB → Set
    data _ where
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
        → (∀ d → PathP (λ i → ℂDesc (indEq i) C𝟙 (indSkeleton tyCtor d)) (D d) (descFor ℓ tyCtor pars d))
        → IndWF (Cμ tyCtor cI D i)





open InductiveCodes {{...}} public


record  ℂwf {{_ : InductiveCodes}} ℓ : Set where
  constructor _|wf|_
  field
    code : ℂ ℓ
    codeWF : IndWF code -- IndWF code

open ℂwf public




wfEl : ∀ {{_ : InductiveCodes}} {{æ : Æ}} {ℓ} → ℂwf ℓ → Set
wfEl {{ æ = æ}} c = El {{æ = æ}} (code c)



wfApproxEl : ∀ {{_ : InductiveCodes}} {ℓ} → ℂwf ℓ → Set
wfApproxEl  c = El {{æ = Approx}} (code c)
