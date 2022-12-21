{-# OPTIONS --cubical --guarded #-}
open import Cubical.Data.Nat
open import Cubical.Foundations.Prelude
open import DecPEq

module GNat where

data GNat : Type where
    Nat⁇ Nat℧ : GNat
    GZero : GNat
    GSuc : GNat → GNat

CℕtoNat : GNat → ℕ
CℕtoNat Nat⁇ = 0
CℕtoNat Nat℧ = 0
CℕtoNat GZero = 0
CℕtoNat (GSuc x) = ℕ.suc (CℕtoNat x)

CℕfromNat : ℕ → GNat
CℕfromNat ℕ.zero = GZero
CℕfromNat (ℕ.suc x) = GSuc (CℕfromNat x)

Cℕembed : ∀  x → CℕtoNat  (CℕfromNat x) ≡ x
Cℕembed ℕ.zero = reflc
Cℕembed (ℕ.suc x) = congPath ℕ.suc (Cℕembed x)
