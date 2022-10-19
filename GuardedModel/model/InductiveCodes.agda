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
open import Cubical.Data.Unit renaming (Unit to 𝟙)
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
data DataGermIsCode (ℓ : ℕ) {{æ : Æ}}  : ∀ {sig} {B+ : Set} {B- : B+ → Set} → GermCtor B+ B- sig → Set2  where
 GEndCode : ∀ {B+ B- } → DataGermIsCode ℓ {B+ = B+} {B- } GEnd
 GRecCode : ∀ {B+ B- sig} {D : GermCtor B+ B- sig}
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GRec D)
 GArgCode : ∀ {B+ B- sig}  {(A+ , A-) : +-Set B+ B- } {D : GermCtor _ _ sig}
   → (c+ : B+ → ℂ ℓ)
   → (c- : (b+ : B+) → A+ b+ → B- b+ → ℂ ℓ)
   → (iso+ : ∀ b+ → Iso (A+ b+) (El (c+ b+)))
   → (iso- : ∀ b+ a+ b- → Iso  (A- b+ a+ b-) (▹ El (c- b+ a+ b-)))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GArg (A+ , A-) D)
 GHRecCode : ∀ {B+ B- sig} {(A+ , A-) : +-Set B+ B- } {D : GermCtor B+ B- sig}
   → (c+ : B+ → ℂ ℓ)
   → (c- : (b+ : B+) → A+ b+ → B- b+ → ℂ ℓ)
   → (iso+ : ∀ b+ → Iso (A+ b+) (Approxed (λ {{æ'}} → El ⦃ æ = æ' ⦄ (c+ b+))))
   → (iso- : ∀ b+ a+ b- → Iso  (A- b+ a+ b-) (▹ (Approxed (λ {{æ'}} → El ⦃ æ = æ' ⦄ (c- b+ a+ b-)))))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GHRec (A+ , A-) D)
 GUnkCode : ∀ {B+ B- sig} {(A+ , A-) : +-Set B+ B- } {D : GermCtor B+ B- sig}
   → (c+ : B+ → ℂ ℓ)
   → (c- : (b+ : B+) → A+ b+ → B- b+ → ℂ ℓ)
   → (iso+ : ∀ b+ → Iso (A+ b+) (Approxed (λ {{æ'}} → El ⦃ æ = æ' ⦄ (c+ b+))))
   → (iso- : ∀ b+ a+ b- → Iso  (A- b+ a+ b-) (▹ (Approxed (λ {{æ'}} → El ⦃ æ = æ' ⦄ (c- b+ a+ b-)))))
   → DataGermIsCode ℓ D
   → DataGermIsCode ℓ (GUnk (A+ , A-) D)

-- Helpful function for showing that, in approx mode, any two of our "negative" values are equal
negUnique : ∀ {{æ : Æ}} {ℓ} {A- X : Set ℓ}
   → æ ≡p Approx
   → (iso- :  Iso  A- (▹ X))
   → (x y : A-)
   → x ≡ y
negUnique reflp iso- x y =
  sym (Iso.leftInv iso- x)
  ∙ cong (Iso.inv iso-) refl
  ∙ Iso.leftInv iso- y


ΣnegUnique : ∀ {{æ : Æ}} {ℓ} {A+ : Set ℓ} {A- X : A+ → Set ℓ}
   → æ ≡p Approx
   → (iso- : ∀ {a+} →  Iso  (A- a+) (▹ (X a+)))
   → (x y : Σ A+ A-)
   → fst x ≡ fst y
   → x ≡ y
ΣnegUnique æeq iso- x y pf = ΣPathP (pf , toPathP (negUnique  æeq iso- _ (snd y)) )

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
      → DataGermIsCode ℓ (preDataGerm ℓ tyCtor (▹⁇ ℓ) d)
  -- Now that ⁇ is defined we can tie the knot
  germForCtor : {{_ : Æ}} → ℕ → (tyCtor : CName) →  (d : DName tyCtor) → GermCtor 𝟙 (λ _ → 𝟙) (indSkeleton tyCtor d)
  germForCtor  ℓ tyCtor d = preDataGerm ℓ tyCtor (▹⁇ ℓ) d
  -- FGerm : {{ _ : Æ }} → ℕ → (c : CName) → Set → Set
  -- FGerm ℓ c Unk = W̃ {!!} {!!} --W̃ (germContainer ℓ c (▹⁇ ℓ)) Unk tt

  AllDataContainer : {{_ : Æ}} → ℕ →  Container (Maybe CName)
  AllDataContainer ℓ = preAllDataContainer ℓ (ℂ-1 {ℓ = ℓ}) (El-1 {ℓ = ℓ}) (▹⁇ ℓ)

  DataGermContainer : {{_ : Æ}} → ℕ → (tyCtor : CName) → DName tyCtor → Container (Maybe CName)
  DataGermContainer ℓ tyCtor d = interpGermCtor (germForCtor ℓ tyCtor d)



  AllDataTypes : {{_ : Æ}} → ℕ → Maybe CName → Set
  AllDataTypes ℓ = preAllDataTypes ℓ (ℂ-1 {ℓ = ℓ}) (El-1 {ℓ = ℓ})  (▹⁇ ℓ)

  DescFunctor : ∀ {{æ : Æ}}  ℓ {B+ B- sig} (tyCtor : CName) → (D : GermCtor B+ B- sig)
    → (b+ : B+)
    → (b- : B- b+)
    → Set
  DescFunctor ℓ tyCtor D b+ b- = FContainer (interpGermCtor' D b+ b- ) (AllDataTypes ℓ) (just tyCtor)

  GermUnkFunctor : {{_ : Æ}} →  ℕ → Set
  GermUnkFunctor ℓ = FContainer (AllDataContainer ℓ) (AllDataTypes ℓ) nothing

  DataGerm : {{ æ : Æ }} → (ℓ : ℕ) → (c : CName) → Set
  DataGerm ℓ c = AllDataTypes ℓ (just c)
  -- FCGerm : ∀ {{æ : Æ}} ℓ {B+ B- sig} (tyCtor : CName)
  --   → (D : GermCtor B+ B- sig)
  --   → (b+ : B+)
  --   → (b- : B- b+)
  --   → Set
  -- FCGerm ℓ tyCtor D b+ b- = {!!} --TODO put back
  -- FContainer (interpGermCtor' D b+ b- ) (W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ)) (⁇Ty ℓ) tt
  DataGermRec : ∀ {{_ : Æ}} {ℓ} (P : Set)
    -- Unk case
    → ((x : GermUnkFunctor ℓ) → □ (AllDataContainer ℓ) (λ _ → P) (nothing , x) → P)
    -- DataGerm case
    → (∀ {tyCtor} (d : DName tyCtor) (x : FContainer (DataGermContainer ℓ tyCtor d) (AllDataTypes ℓ) (just tyCtor)) → □ {X = AllDataTypes ℓ} (DataGermContainer ℓ tyCtor d) (λ _ → P) (_ , x) → P)
    → (Maybe CName → P × P)
    → ∀ {mc} → AllDataTypes ℓ mc → P
  DataGermRec P unk rec base {nothing} (Wsup (FC com resp)) = unk (FC com resp) λ r → DataGermRec P unk rec base (resp r)
  DataGermRec P unk rec base {just x₁} (Wsup (FC (d , com) resp)) =
    rec
      d
      (FC com resp)
      (λ r → DataGermRec P unk rec base (resp r))
  DataGermRec  P unk rec base {i} W℧ = fst (base i)
  DataGermRec  P unk rec base {i} W⁇ = snd (base i)



  -- Predicate that determines if a code is well formed
  -- with respect to the inductive types it refers to
  -- i.e. if it's an instantation of that type's parameters and indices
  -- interleaved mutual
  --   data IndWF {ℓ} : ℂ ℓ → Set
  --   -- data DescIndWF {ℓ} {cI cB : ℂ ℓ } : ℂDesc cI cB → Set
  --   data _ where
  --     IWF⁇ : IndWF C⁇
  --     IWF℧ : IndWF C℧
  --     IWF𝟘 : IndWF C𝟘
  --     IWF𝟙 : IndWF C𝟙
  --     IWFType : ∀ {{_ : 0< ℓ}} → IndWF CType
  --     IWFΠ : ∀ {dom cod}
  --       → IndWF dom
  --       → (∀ x → IndWF (cod x))
  --       → IndWF (CΠ dom cod)
  --     IWFΣ : ∀ {dom cod}
  --       → IndWF dom
  --       → (∀ x → IndWF (cod x))
  --       → IndWF (CΣ dom cod)
  --     IWF≡ : ∀ {c x y} → IndWF c → IndWF (C≡ c x y)
  --     IWFμ : ∀ {tyCtor cI D i}
  --       → (pars : ApproxEl (Params ℓ tyCtor))
  --       → (indEq : cI ≡ Indices ℓ tyCtor pars)
  --       → (∀ d → PathP (λ i → ℂDesc (indEq i) C𝟙 (indSkeleton tyCtor d)) (D d) (descFor ℓ tyCtor pars d))
  --       → IndWF (Cμ tyCtor cI D i)





open InductiveCodes {{...}} public


-- record  ℂwf {{_ : InductiveCodes}} ℓ : Set where
--   constructor _|wf|_
--   field
--     code : ℂ ℓ
--     codeWF : IndWF code -- IndWF code

-- open ℂwf public




-- wfEl : ∀ {{_ : InductiveCodes}} {{æ : Æ}} {ℓ} → ℂwf ℓ → Set
-- wfEl {{ æ = æ}} c = El {{æ = æ}} (code c)



-- wfApproxEl : ∀ {{_ : InductiveCodes}} {ℓ} → ℂwf ℓ → Set
-- wfApproxEl  c = El {{æ = Approx}} (code c)
