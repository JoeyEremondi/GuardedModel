-- Inductive Descriptions for Gradual Datatypes

open import Level
open import Cubical.Data.Nat renaming (Unit to 𝟙)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty renaming (⊥ to 𝟘)
open import Cubical.Relation.Nullary
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Bool renaming (Bool to 𝟚)
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Sum as Sum
open import Cubical.Data.FinData
-- Bool is the gradual unit type, true is tt and false is ℧

open import Cubical.Data.Sum
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
open import DecPEq
open import Cubical.Functions.FunExtEquiv using (funExtDep)

-- open import Cubical.Data.Bool
open import GuardedAlgebra
import GuardedModality as G

open import ApproxExact
open import Util
module W where

record Container (I : Set)  : Set1 where
  constructor _◃_/_
  field
    Command  : (i : I) → Set
    Response : ∀ {i} → Command i → Set
    -- ResponseÆ : ∀ {i} → Command i → Set
    -- ResponseUnk : ∀ {i} → Command i → Set
    inext     : ∀ {i} (c : Command i) → Response c → I

open Container public


record ⟦_⟧F {{æ : Æ}} {I} (C : Container I) (X : Æ → I → Set) (i : I) : Set where
  constructor FC
  field
    command : Command C i
    response :
      (r : Response C command)
      → X Approx (inext C command r)
    responseExact :
      (IsExact æ)
      → (r : Response C command)
      → LÆ (X æ (inext C command r))
    -- responseLater :
    --   (r : Response C command)
    --   → ∀ j
    --   → j ≅ inext C command r
    --   → LÆ (X j)
    -- responseUnk : ResponseUnk C command → Unk


⟦_⟧F[_] : ∀ {I} (C : Container I) → Æ → (X : ( æ : Æ ) → I → Set)  → (i : I) → Set
⟦_⟧F[_] C æ = ⟦_⟧F {{æ = æ}} C

-- Functoral action aka good old map
FMap : ∀ {{æ : Æ}} {I} {C : Container I} {X Y : Æ → I → Set} {i : I} → (∀ {æ i} → X æ i → Y æ i) → ⟦ C ⟧F X i → ⟦ C ⟧F Y i
FMap f (FC com resp respEx) = FC com (λ r → f (resp r)) retExact
  where
    retExact : _ → (r : _) → _
    retExact pf r = do
      fr ← respEx pf r
      pure (f fr)

-- Can only do properties of the approximate parts
□ : ∀ {æ : Æ} {ℓ I} {X : Æ → I → Set} (C : Container I) →  (∀ {æ} → (Σ I (X æ)) → Set ℓ) → (Σ I (⟦ C ⟧F[ æ ] X)) → Set ℓ
□ C P (i , (FC c k kex)) = ∀ r → P (inext C c r , k r)

data W̃ {{æ : Æ}} {I : Set} (C : Æ → Container I) (i : I)  :  Set where
  Wsup : ⟦ C æ ⟧F  (λ æ' → W̃ {{æ = æ'}} C) i → W̃ C i
  W℧ W⁇ : W̃ C i
  -- Projections.


-- Given a container for each a : A, produce the new container
-- that is the sum of all those containers.
-- Useful for encoding data constructors encoded as Fin
Arg : ∀ {A I : Set} → (A → Container I) → Container I
Command (Arg {A} f) i = Σ[ a ∈ A ] Command (f a) i
Response (Arg f) (a , com) = Response (f a) com
inext (Arg f) (a , com) r = inext (f a) com r
