{-# OPTIONS --cubical --guarded #-}
open import Cubical.Data.Nat
open import Cubical.Foundations.Prelude
open import DecPEq
open import Cubical.Data.Bool

module GTypes where


data G𝟙 : Set where
  Gtt ℧𝟙 : G𝟙


is-tt : G𝟙 → Bool
is-tt Gtt = true
is-tt ℧𝟙 = false

data G𝟘 : Set where
  ℧𝟘 : G𝟘


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
