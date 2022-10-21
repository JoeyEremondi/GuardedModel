{-# OPTIONS --cubical --guarded #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.FinData
open import Cubical.Data.Equality
open import Cubical.Data.Sigma
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import GuardedAlgebra
open import ApproxExact

module HeadDefs (numCtors : ℕ) where

data TyHead : Set where
  HΠ : TyHead
  HΣ : TyHead
  H≅ : TyHead
  H𝟙 : TyHead
  H𝟘 : TyHead
  HType : TyHead
  HCumul : TyHead
  HCtor : Fin numCtors → TyHead

data GHead : Set where
  H⁇ : GHead
  H℧ : GHead
  HStatic : TyHead → GHead

HStatic-inj : ∀ {h1 h2} → HStatic h1 ≡p HStatic h2 → h1 ≡p h2
HStatic-inj reflp = reflp