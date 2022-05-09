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
--
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
