open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.FinData

module Constructors where

-- Used to classify the "skeleton" of inductive types before we've defined codes
data IndSig : Set where
  SigE : IndSig
  SigA SigR : ℕ → IndSig → IndSig




record DataTypes : Set1 where
  field
    numTypes : ℕ
  CName : Set
  CName = Fin numTypes
  field
    numCtors : CName → ℕ
    -- indSig : CName → IndSig
  DName : CName → Set
  DName tyCtor = Fin (numCtors tyCtor)
  field
    -- Signature for each datatype
    indSkeleton : (tyCtor : CName) → DName tyCtor → IndSig

open DataTypes {{...}} public
