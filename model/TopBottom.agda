{-# OPTIONS --cubical --guarded #-}

open import GuardedAlgebra
open import Cubical.Data.Maybe
open import Cubical.Data.Empty
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Bool renaming (Bool to 𝟚)
open import Cubical.Data.FinData hiding (elim)
open import Cubical.Data.Prod
open import Cubical.Data.Sigma
open import Inductives
open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients as Q

module TopBottom {{_ : GuardedAlgebra}} {{_ : Datatypes}} where

open import Code
open import Util

ℂis℧Bool : ∀ {ℓ} → ℂ ℓ → 𝟚
ℂis℧Bool CodeModule.C℧ = true
ℂis℧Bool _ = false

ℂ℧True : ∀ {ℓ} {c : ℂ ℓ} → ℂis℧Bool c ≡p true → c ≡ C℧
ℂ℧True {c = CodeModule.C⁇} ()
ℂ℧True {c = CodeModule.C℧} reflp = refl
ℂ℧True {c = CodeModule.C𝟘} ()
ℂ℧True {c = CodeModule.C𝟙} ()
ℂ℧True {c = CodeModule.CType} ()
ℂ℧True {c = CodeModule.CΠ c cod} ()
ℂ℧True {c = CodeModule.CΣ c cod} ()
ℂ℧True {c = CodeModule.C≡ c x y} ()
ℂ℧True {c = CodeModule.Cμ tyCtor c D x} ()


ℂ℧False : ∀ {ℓ} {c : ℂ ℓ} → ℂis℧Bool c ≡p false → ¬ (c ≡ C℧)
ℂ℧False {c = c} bpf eqpf with () ← true≢false (cong ℂis℧Bool (sym eqpf) ∙ (propToPathDec bpf))


ℂis℧ : ∀ {ℓ} → (c : ℂ ℓ) → Dec (c ≡ C℧)
ℂis℧ c with ℂis℧Bool c in eq
... | true = yes (ℂ℧True eq)
... | false = no (ℂ℧False eq)

dec≡℧ : ∀ {ℓ} (x : ⁇ ℓ) → Dec (℧≡ x)
dec≡℧ CodeModule.⁇⁇ = no (λ ())
dec≡℧ CodeModule.⁇℧ = yes ℧℧
dec≡℧ CodeModule.⁇𝟙 = no (λ ())
dec≡℧ {suc ℓ} (CodeModule.⁇Type x) with ℂis℧ x
... | yes pf = yes (transport eq ⁇Type℧)
 where
   eq : ℧≡ (⁇Type C℧) ≡ ℧≡ (⁇Type x)
   eq = cong ℧≡ (cong ⁇Type (sym pf))
... | no npf  = no (λ { ⁇Type℧ → npf refl} )
dec≡℧ (CodeModule.⁇TypeSelf x)  = {!!}
dec≡℧ (CodeModule.⁇Π x) = {!!}
dec≡℧ (CodeModule.⁇Σ x) = {!!}
dec≡℧ (CodeModule.⁇≡ x) = {!!}
dec≡℧ (CodeModule.⁇μ tyCtor ctor x) = {!!}


-- ℧≡Prop : ∀ {ℓ} (x : ⁇ ℓ) → isProp (⁇℧ ≡ x)
-- ℧≡Prop x = ⁇IsSet ⁇℧ x

-- pathEnd : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p : x ≡ y) → ∀ i → x ≡ p i
-- pathEnd p i j = p (i ∧ j)


-- ⁇is℧True : ∀ {ℓ} (x : ⁇ ℓ) → ⁇is℧Bool x ≡p true → ⁇℧ ≡ x
-- ⁇is℧True CodeModule.⁇℧ pf = refl
-- ⁇is℧True {ℓ = suc ℓ} (CodeModule.⁇Type CodeModule.C℧) pf = ⁇℧≡ (⁇Type C℧) ⁇Type℧
-- ⁇is℧True (CodeModule.⁇Π f) pf = ⁇℧≡ (⁇Π f) (⁇Π℧ ( (⁇is℧True (f topArg) pf)))
-- ⁇is℧True {ℓ} (CodeModule.⁇Σ (x , y)) pf = ⁇℧≡ (⁇Σ (x , y)) (transport (cong ℧≡ (cong ⁇Σ pxy)) ⁇Σ℧)
--   where
--     px : ⁇℧ ≡ x
--     py : ⁇℧ ≡ y
--     pxy : (⁇℧ , ⁇℧) ≡ (x , y)
--     pxy = cong₂ {A = ⁇ ℓ} {B = λ _ → ⁇ ℓ} {C = λ _ _ → ⁇ ℓ Cubical.Data.Prod.× ⁇ ℓ} _,_ px py
--     px = ⁇is℧True x (proj₁ (andBoth (⁇is℧Bool x) (⁇is℧Bool y) (propToPathDec pf)))
--     py = ⁇is℧True y (proj₂ (andBoth (⁇is℧Bool x) (⁇is℧Bool y) (propToPathDec pf)))
-- ⁇is℧True (CodeModule.⁇≡ x) pf = ⁇℧≡ (⁇≡ x) (subst (λ x → ℧≡ (⁇≡ x)) (⁇is℧True x pf) ⁇≡℧)
-- ⁇is℧True (CodeModule.⁇μ tyCtor ctor μ℧) pf = ⁇℧≡ (⁇μ tyCtor ctor μ℧) (⁇μ℧ tyCtor ctor)
-- ⁇is℧True (CodeModule.⁇℧≡ x rel i) pf =  isProp→PathP (λ j → ℧≡Prop (⁇℧≡ x rel j)) refl (⁇is℧True x (subst {x = ⁇℧≡ x rel i} {y = x} (λ z → ⁇is℧Bool z ≡p true) ? pf)) i -- ⁇IsSet ⁇℧ (⁇℧≡ x rel i) {!⁇is℧True !} {!!} i -- ⁇℧ ≡ ⁇℧≡ x rel i
-- ⁇is℧True (CodeModule.⁇IsSet x y p1 p2 i i₁) pf = {!!}
-- -- ⁇is℧True CodeModule.⁇℧ pf = refl
-- -- ⁇is℧True { ℓ = suc ℓ} (CodeModule.⁇Type x) pf = cong ⁇Type (ℂ℧True pf) ∙ ⁇Type℧
-- -- ⁇is℧True {ℓ = suc ℓ} (CodeModule.⁇Type℧ i) pf j = ⁇IsSet {!!} refl i j
-- -- ⁇is℧True (CodeModule.⁇Π x) pf = {!!}
-- -- ⁇is℧True (CodeModule.⁇Π℧ x i) pf = {!!}
-- -- ⁇is℧True (CodeModule.⁇Σ x) pf = {!!}
-- -- ⁇is℧True (CodeModule.⁇Σ℧ i) pf = {!!}
-- -- ⁇is℧True (CodeModule.⁇≡ x) pf = {!!}
-- -- ⁇is℧True (CodeModule.⁇≡℧ i) pf = {!!}
-- -- ⁇is℧True (CodeModule.⁇μ tyCtor ctor x) pf = {!!}
-- -- ⁇is℧True (CodeModule.⁇μ℧ tyCtor ctor i) pf = {!!}
-- -- ⁇is℧True (CodeModule.⁇IsSet p1 p2 i j) pf = {!!}

-- -- -- -- ⁇℧True : ∀ {ℓ} (x : ⁇ ℓ) → ⁇is℧Bool x ≡ true → x ≡ ⁇℧

-- -- -- -- ⁇℧False : ∀ {ℓ} {x : ⁇ ℓ} → ⁇is℧Bool x ≡ false → ¬ (x ≡ ⁇℧)
-- -- -- -- ⁇℧False {x = x} bpf eqpf with () ← true≢false (cong ⁇is℧Bool (sym eqpf) ∙ bpf)
