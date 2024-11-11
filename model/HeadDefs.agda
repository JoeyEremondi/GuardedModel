
-- open import Guarded
open import Level

open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality

open import GuardedAlgebra
open import ApproxExact

open import Constructors

module HeadDefs {{_ : DataTypes}}  where

data TyHead : Set where
  HΠ : TyHead
  HΣ : TyHead
  H≅ : TyHead
  H𝟙 : TyHead
  H𝟘 : TyHead
  Hℕ : TyHead
  HType : TyHead
  HCumul : TyHead
  HCtor : Fin numTypes → TyHead

data GHead : Set where
  H⁇ : GHead
  H℧ : GHead
  HStatic : TyHead → GHead

HStatic-inj : ∀ {h1 h2} → HStatic h1 ≡ HStatic h2 → h1 ≡ h2
HStatic-inj refl = refl
