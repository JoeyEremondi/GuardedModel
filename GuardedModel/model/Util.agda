{-# OPTIONS --cubical --guarded #-}


module Util where

open import Cubical.Data.Maybe
open import Cubical.Relation.Nullary
open import DecPEq
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Bool renaming (Bool to 𝟚)
open import Cubical.Data.FinData hiding (elim)
-- open import Cubical.Data.Prod
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty

open import Agda.Builtin.Reflection
open import Agda.Primitive public

andBoth : ∀ (b1 b2 : 𝟚) → (b1 and b2) ≡ true → (b1 ≡p true) × (b2 ≡p true)
andBoth false false pf with () ← true≢false (sym pf)
andBoth false true pf with () ← true≢false (sym pf)
andBoth true false pf with () ← true≢false (sym pf)
andBoth true true pf = reflp , reflp


default : {A : Set} → A → Term → TC Unit
default x hole = bindTC (quoteTC x) (unify hole)


_ℕ+_ : ℕ → Level → Level
zero  ℕ+ ℓ = ℓ
suc n ℕ+ ℓ = lsuc (n ℕ+ ℓ)

#_ : ℕ → Level
#_ = _ℕ+ lzero


data #_-1≡_ : ℕ -> Level -> Set where
  instance is-lsuc : ∀ {ℓ} -> #(suc ℓ) -1≡ # ℓ

Set-1 : (ℓ : ℕ ) -> Set (# ℓ)
Set-1 zero  = Unit*
Set-1 (suc ℓ) = Set (# ℓ)


ToSort : ∀ {ℓ} -> Set-1 ℓ -> Set (# ℓ)
ToSort {suc ℓ} s = Lift s
ToSort {zero} s = ⊥

typeof : ∀ {ℓ} {A : Set ℓ} → A → Set ℓ
typeof {A = A} _ = A


pathi0 : ∀ {A : Set} {x y : A} → (pf : x ≡c y) → ∀ i → pf i ≡c pf i0
pathi0 pf i j = pf (i ∧ ~ j)

pathi1 : ∀ {A : Set} {x y : A} → (pf : x ≡c y) → ∀ i → pf i ≡c pf i1
pathi1 pf i  = pathi0 (sym pf) (~ i)
