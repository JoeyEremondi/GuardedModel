{-# OPTIONS --cubical --guarded #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
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

module HeadDefs (numCtors : â) where

data TyHead : Set where
  HÎ  : TyHead
  HÎ£ : TyHead
  Hâ : TyHead
  Hð : TyHead
  Hð : TyHead
  Hâ : TyHead
  HType : TyHead
  HCumul : TyHead
  HCtor : Fin numCtors â TyHead

data GHead : Set where
  Hâ : GHead
  Hâ§ : GHead
  HStatic : TyHead â GHead

HStatic-inj : â {h1 h2} â HStatic h1 â¡p HStatic h2 â h1 â¡p h2
HStatic-inj reflp = reflp
