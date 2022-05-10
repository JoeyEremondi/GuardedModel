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
data IsGuardedCode {ℓ} {{æ : Æ}} : ℂ ℓ → Set → Set1
codeToGuarded : ∀ {ℓ} {{æ : Æ}} {c : ℂ ℓ} {A : Set} → IsGuardedCode c A → El {{æ = æ}} c → A
data DataGermIsCode (ℓ : ℕ) {{æ : Æ}}  : {B : Set} → GermCtor B → Set1

data IsGuardedCode {{æ1}} where
  IsGRefl : ∀ {A } c → Iso A (El c) → IsGuardedCode c A
  IsGGuarded : ∀ {A c} → IsGuardedCode c A → IsGuardedCode c (▹ A)
  IsGΠ  : ∀ {dom} {cod} {Dom : {{æ : Æ}} → Set} {Cod : Dom {{Approx}} → Set}
    → (pf : ∀ {{æ}} → IsGuardedCode  {{æ}} dom (Dom {{æ}}))
    → ((x : (ApproxEl dom)) → IsGuardedCode (cod x) (Cod (codeToGuarded {{Approx}} (pf {{Approx}}) x)))
    → IsGuardedCode (CΠ dom cod)  ((x : Approxed (λ {{æ}} → Dom {{æ}}) {{æ1}} ) → Cod (approx x))
  IsGΣ  : ∀ {dom} {cod} {Dom : {{æ : Æ}} → Set} {Cod : Dom {{Approx}} → Set}
    → (pf : ∀ {{æ}} → IsGuardedCode  {{æ}} dom (Dom {{æ}}))
    → ((x : (ApproxEl dom)) → IsGuardedCode (cod x) (Cod (codeToGuarded {{Approx}} (pf {{Approx}}) x)))
    → IsGuardedCode (CΣ dom cod)  (Σ[ x ∈ Approxed (λ {{æ}} → Dom {{æ}}) {{æ1}} ] Cod (approx x))
  IsG≡ : ∀ {c} {A : {{æ : Æ}} → Set} (x y : ApproxEl c)
    → (pf : ∀ {{æ}} → IsGuardedCode  {{æ}} c (A {{æ}}))
    → IsGuardedCode (C≡ c x y) (codeToGuarded {{Approx}} (pf {{Approx}}) x ≅ codeToGuarded {{Approx}} (pf {{Approx}}) y)
  -- There's no case for inductives: any inductives must either be encoded direclty, or put directly behind the guarded modality
  -- TODO: is this right?
  -- IsGμ : ∀ (tyCtor : CName) (D : DName tyCtor → GermCtor Unit)  → (∀ d → DataGermIsCode ℓ (D d)) → IsGuardedCode ℓ (FGerm ℓ tyCtor (▹⁇ ℓ) (⁇Ty ℓ))

-- Predicate classifying whether a datagerm description is equivalent to a ℂDesc
--TODO: do we still need this with the more strict code requirements?

data DataGermIsCode ℓ where
 GEndCode : ∀ {B} → DataGermIsCode ℓ {B} GEnd
 GRecCode : ∀ {B} {D : GermCtor B}
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GRec D)
 GArgCode : ∀ {B} {A : B → Set} {D : GermCtor (Σ B A)} → (c : B → ℂ ℓ) → (∀ b → IsGuardedCode (c b) (A b))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GArg A D)
 GHRecCode : ∀ {B} {A : B → Set} {D : GermCtor B} → (c : B → ℂ ℓ) → (∀ b → IsGuardedCode (c b) (A b))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GHRec A D)
 GUnkCode : ∀ {B} {A : B → Set} {D : GermCtor B} (c : B → ℂ ℓ) → (∀ b → IsGuardedCode (c b) (A b))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GUnk A D)

codeToGuarded (IsGRefl _ isom) x = Iso.inv isom x
codeToGuarded (IsGGuarded pf) x = next (codeToGuarded pf x)
codeToGuarded ⦃ æ = Approx ⦄ (IsGΠ pdom pcod) f x = {!!}
codeToGuarded ⦃ æ = Exact ⦄ (IsGΠ pdom pcod) f x = {!!}
codeToGuarded (IsGΣ pf x₁) x = {!!}
codeToGuarded (IsG≡ x₁ y pf) x = {!!}

-- underlyingCode : ∀ {ℓ A} → IsGuardedCode ℓ {{Approx}} A → ℂ ℓ
-- toUnderlying : ∀ {{_ : Æ}} {ℓ A} → (pf : ∀ {{æ}} → IsGuardedCode ℓ {{æ}} A) → A → El (underlyingCode (pf {{Approx}}))
-- fromUnderlying : ∀ {{_ : Æ}} {ℓ A} → (pf : IsGuardedCode ℓ {{Approx}} A) → El (underlyingCode pf) → A

-- underlyingCode (IsGRefl c x) = c
-- underlyingCode (IsGGuarded pf) = underlyingCode pf
-- underlyingCode (IsGΠ dpf cpf) = CΠ (underlyingCode (dpf {{Approx}})) λ x → underlyingCode (cpf (fromUnderlying {{Approx}} (dpf {{Approx}}) x))
-- underlyingCode (IsGΣ dpf cpf) = CΣ (underlyingCode (dpf {{Approx}})) λ x → underlyingCode (cpf (fromUnderlying {{Approx}} (dpf {{Approx}}) x))
-- underlyingCode (IsG≡ x y pf) = C≡ (underlyingCode pf) (toUnderlying ⦃ Approx ⦄ {!λ {{_}} → pf!} x) (toUnderlying {{Approx}} {!!} y)

-- toUnderlying (IsGRefl c isom) x = Iso.fun isom x
-- toUnderlying (IsGGuarded pf) x = {!!}
-- toUnderlying (IsGΠ x₁ x₂) x = {!!}
-- toUnderlying (IsGΣ x₁ x₂) x = {!!}
-- toUnderlying (IsG≡ x₁ y pf) x = {!!}
-- underlyingCode (IsGμ tyCtor D x) = Cμ tyCtor {!!} {!!} {!!}

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
