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
    paramLevel : (ℓ : ℕ) → CName → ℕ
    posParams : (ℓ : ℕ) → (tyCtor : CName) → ℂ (paramLevel ℓ tyCtor)
    negParams : (ℓ : ℕ) → (tyCtor : CName) → ApproxEl (posParams ℓ tyCtor) → ℂ (paramLevel ℓ tyCtor)
    posIndices : (ℓ : ℕ) → (tyCtor : CName) → ApproxEl (posParams ℓ tyCtor) → ℂ ℓ
    negIndices : (ℓ : ℕ) → (tyCtor : CName)
      → (par⁺ : ApproxEl (posParams ℓ tyCtor))
      → (par⁻ : ApproxEl (negParams ℓ tyCtor par⁺))
      → (ind⁺ : ApproxEl (posIndices ℓ tyCtor par⁺))
      → ℂ ℓ
    descFor : (ℓ : ℕ) → (tyCtor : CName)
      → (par⁺ : ApproxEl (posParams ℓ tyCtor))
      → (par⁻ : ApproxEl (negParams ℓ tyCtor par⁺))
      → (d : DName tyCtor)
      → ℂDesc (CΣ (posIndices ℓ tyCtor par⁺) (λ ind⁺ → negIndices ℓ tyCtor par⁺ par⁻ ind⁺)) C𝟙
    germWF : {{_ : Æ}} → (ℓ : ℕ) → (tyCtor : CName)
      → Σ[ par⁺ ∈ {!!} ]
        Iso
          (FGerm ℓ tyCtor (▹⁇ ℓ) (⁇Ty ℓ))
          {!!}

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
     → (par⁺ : ApproxEl (posParams ℓ tyCtor))
     → (par⁻ : ApproxEl (negParams ℓ tyCtor par⁺))
     → (indEq : cI ≡ CΣ (posIndices ℓ tyCtor par⁺) (negIndices ℓ tyCtor par⁺ par⁻))
     → (∀ d → PathP (λ i → ℂDesc (indEq i) C𝟙) (D d) (descFor ℓ tyCtor par⁺ par⁻ d))
     → IndWF (Cμ tyCtor cI D i)


-- record DataGermCodes : Set2 where
--   field
--     -- dataGermCode : ∀ ℓ → (c : CName) → DName c → ℂDesc (C𝟙 {ℓ = ℓ})
--     dataGermIsCode : ∀ {{_ : Æ}} ℓ (tyCtor : CName) → (d : DName tyCtor)
--       → DataGermIsCode ℓ (dataGerm ℓ tyCtor (dfix (F⁇ {ℓ})) d)
--     -- dataGermSize : ∀ {ℓ} (tyCtor : CName) → W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ) tt → Ord
--     -- dataGermCodeEq : ∀ ℓ → (tyCtor : CName) → ℂμ tyCtor (dataGermCode ℓ tyCtor) true ≡ W (Arg (dataGerm tyCtor (dfix (F⁇ {ℓ})))) (⁇Ty ℓ) tt
--     -- dataGermFEq : ∀ ℓ {X : Set} → (tyCtor : CName) → (d : DName tyCtor) → ℂDescEl (dataGermCode ℓ tyCtor d) (λ _ → X) true ≡ FContainer (dataGerm tyCtor (dfix (F⁇ {ℓ})) d) (λ _ → X) (⁇Ty ℓ) tt

-- open DataGermCodes {{...}} public


-- -- --The result gives something equivalent to the non-coded Arg function in Inductives.agda
