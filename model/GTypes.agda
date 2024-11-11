open import Data.Nat
open import Data.Bool
open import FunExt

module GTypes where


data G𝟙 : Set where
  Gtt ℧𝟙 : G𝟙

𝟙meet : G𝟙 → G𝟙 → G𝟙
𝟙meet Gtt Gtt = Gtt
𝟙meet _ _ = ℧𝟙


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
Cℕembed ℕ.zero = refl
Cℕembed (ℕ.suc x) = cong ℕ.suc (Cℕembed x)



natMeet : GNat → GNat → GNat
natMeet Nat⁇ y = y
natMeet x Nat⁇ = x
natMeet GZero GZero = GZero
natMeet (GSuc x) (GSuc y) = GSuc (natMeet x y)
natMeet _ _ = Nat℧
