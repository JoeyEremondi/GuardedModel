

{-# OPTIONS --cubical --guarded #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Equality
open import Inductives
open import GuardedAlgebra
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude

open import ApproxExact
open import InductiveCodes
open import CodeSize
open import WMuEq

module Germ {{_ : DataTypes}} {{_ : DataGerms}} {{_ : InductiveCodes}} {{_ : DataGermsSmaller}} where

open import Code
open import Head
open import Util
open import Ord
-- open Ord ℂ El ℧ C𝟙 refl



germ : {{_ : Æ}} → TyHead → (ℓ : ℕ) → Set -- ℂ ℓ
germ HΠ ℓ = (x : ⁇Ty ℓ) → ⁇Ty ℓ
germ HΣ ℓ = ⁇Ty ℓ × ⁇Ty ℓ
germ H≅ ℓ = dyn ≅ dyn
  where
    dyn : ⁇Ty ℓ
    dyn = ⁇⁇
germ H𝟙 _ = Bool
germ H𝟘 _ = Unit
germ HType zero = Unit
germ HType (suc ℓ) = ℂ ℓ
germ (HCtor tyCtor) ℓ  = W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ) tt
germ HCumul ℕ.zero = ⊥
germ HCumul (ℕ.suc ℓ) = Σ[ c ∈ ℂ ℓ ]( El c )

germTo⁇ : ∀ {{_ : Æ}} {h ℓ} → (germ h ℓ) → LÆ (⁇Ty ℓ)
germFrom⁇ : ∀ {{_ : Æ}} {ℓ h} → (x : ⁇Ty ℓ) → (unkHead x ≡p HStatic h) → (germ h ℓ)


germTo⁇ {h = HΠ} f = ⦇ ⁇Π (liftFun (λ ▹x → θL ⁇⁇ (map▹ Now (transport hollowEq ▹x)))) ⦈
germTo⁇ {h = HΣ} (x , y) = pure (⁇Σ (x , y))
germTo⁇ {h = H≅} x = pure (⁇≡ x)
germTo⁇ {h = H𝟙} false = pure ⁇℧
germTo⁇ {h = H𝟙} true = pure ⁇𝟙
germTo⁇ {h = H𝟘} tt = pure ⁇℧
germTo⁇ {h = HType} {zero} x = pure ⁇℧
germTo⁇ {h = HType} {suc ℓ} x = pure (⁇Type x)
germTo⁇ {h = HCtor tyCtor} {ℓ} x = pure (⁇μ tyCtor x)
germTo⁇ {h = HCumul} {ℓ = ℕ.suc ℓ} (c , x) = pure (⁇Cumul c x)


germFrom⁇ {h = HΠ} (CodeModule.⁇Π f) eq x = f (transport⁻ hollowEq (next x))
germFrom⁇ {h = H𝟙} CodeModule.⁇𝟙 eq = true
germFrom⁇ {ℕ.suc ℓ} {h = .HType} (CodeModule.⁇Type x) reflp =  x
germFrom⁇ {h = HΣ} (CodeModule.⁇Σ (x , y)) eq =  (x , y)
germFrom⁇ {h = H≅} (CodeModule.⁇≡ x) eq =  x
germFrom⁇ {ℓ} {h = HCtor x₁} (CodeModule.⁇μ tyCtor x) reflp = x --TODO handle err specially?
germFrom⁇ {ℓ = ℕ.suc ℓ} {h = .HCumul} (CodeModule.⁇Cumul c x) reflp = c , x
