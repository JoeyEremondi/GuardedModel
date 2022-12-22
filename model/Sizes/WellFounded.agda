-- Helpers for Cubical.Induction.WellFounded
--

module Sizes.WellFounded where

open import Cubical.Foundations.Prelude
open import Cubical.Induction.WellFounded public
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Agda.Primitive using (_⊔_)
open import Cubical.Data.Bool



∥WellFounded∥ : ∀ {ℓ ℓ'} {A : Type ℓ} {_<_ : A → A → Type ℓ'} → WellFounded _<_ → WellFounded λ x y → ∥ x < y ∥₁
∥WellFounded∥ {_<_ = _<_} wf x = accessProp x (wf x)
  where
    accessProp : ∀ z → Acc _<_ z → Acc (λ x y → ∥ x < y ∥₁ ) z
    accessProp z (acc zacc) = acc (λ y ∣y<z∣ → rec (isPropAcc y) (λ y<z → accessProp y (zacc y y<z)) ∣y<z∣)

--Lexicographic ordering of pairs is well-founded
module _ {ℓa ℓ'a} {A : Type ℓa} {_<a_ : A → A → Type ℓ'a}
  {ℓb ℓ'b} {B : Type ℓb} {_<b_ : B → B → Type ℓ'b} where

  data _<Lex_ : (A × B) → (A × B) → Type (ℓa ⊔ ℓb ⊔ ℓ'a ⊔ ℓ'b) where
    <LexL : ∀ {a a' b b'} → a <a a' → (a , b) <Lex (a' , b')
    <LexR : ∀ {a a' b b'} → a ≡ a' → b <b b' → (a , b) <Lex (a' , b')

  LexWellFounded : WellFounded _<a_ → WellFounded _<b_ → WellFounded _<Lex_
  LexWellFounded wfa wfb (a , b) = acc (helper (wfa a) (wfb b))
    where
      helper : ∀ {a b} → Acc _<a_ a → Acc _<b_ b → WFRec _<Lex_ _ (a , b)
      helper (acc acca) accb (a' , b') (<LexL a'<a) = acc (helper (acca a' a'<a) (wfb b'))
      helper acca (acc accb) (a' , b') (<LexR a≡a' b'<b) = subst (λ x → Acc _ (x , b')) (sym a≡a') (acc (helper acca (accb b' b'<b)))

  ∥LexWellFounded∥ : WellFounded _<a_ → WellFounded _<b_ → WellFounded (λ x y → ∥ x <Lex y ∥₁)
  ∥LexWellFounded∥ wfa wfb = ∥WellFounded∥ (LexWellFounded wfa wfb)


-- order on booleans


data BoolOrder : Bool → Bool → Set where
  false<true : BoolOrder false true

BoolWellFounded : WellFounded BoolOrder
BoolWellFounded false = acc (λ {y ()})
BoolWellFounded true = acc (λ {false false<true → acc λ {_ ()}})


import Cubical.Data.Nat as Nat
import Cubical.Data.Nat.Order as Nat
import Cubical.Data.FinData as Fin

<Fin : ∀ n → (x y : Fin.Fin n) → Type
<Fin n x y = Fin.toℕ x Nat.< Fin.toℕ y

FinAcc : ∀ {n} (x : Fin.Fin n) → Acc (Nat._<_) (Fin.toℕ x) → Acc (<Fin n ) x
FinAcc {n} x (acc accLt) = acc helper
  where
    helper : WFRec (<Fin n) (Acc (<Fin n)) x
    helper y lt = FinAcc y (accLt (Fin.toℕ y) lt)

FinWellFounded : ∀ {n} → WellFounded (<Fin n)
FinWellFounded x = FinAcc x (Nat.<-wellfounded (Fin.toℕ x))
