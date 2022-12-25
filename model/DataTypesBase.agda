module DataTypesBase where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.FinData

data IndSig : Type where
  SigA SigR :  ℕ → IndSig → IndSig
  SigE : IndSig

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
    indSkeleton : (tyCtor : CName) → DName tyCtor → IndSig

open DataTypes {{...}} public
