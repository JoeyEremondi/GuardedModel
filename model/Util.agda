{-# OPTIONS --cubical --guarded --prop #-}


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
open import Cubical.Foundations.Transport
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


pathij : ∀ {ℓ} {A : Set ℓ} {x y : A} → (pf : x ≡c y) → ∀ i j → pf i ≡c pf j
pathij pf i j k = pf (( k ∧ j) ∨ (~ k ∧ i))


pathi0 : ∀ {ℓ} {A : Set ℓ} {x y : A} → (pf : x ≡c y) → ∀ i → pf i ≡c pf i0
pathi0 pf i = pathij pf i i0

pathi1 : ∀ {ℓ} {A : Set ℓ} {x y : A} → (pf : x ≡c y) → ∀ i → pf i ≡c pf i1
pathi1 pf i = pathij pf i i1

compPathEq : ∀ {ℓ} {A : I → Set ℓ} {x : A i0} {y : A i1} {z : A i1} → PathP A x y → y ≡c z → PathP A x z
compPathEq pth peq = substPath (λ w → PathP _ _ w) peq pth

compEqPath : ∀ {ℓ} {A : I → Set ℓ} {x : A i0} {y : A i0} {z : A i1} → x ≡c y → PathP A y z → PathP A x z
compEqPath peq pth = substPath (λ w → PathP _ w _) (sym peq) pth

reflCompose : ∀ {ℓ} {A : Set ℓ} {x : A} → (refl {x = x} ) ≡c refl ∙ refl
reflCompose {x = x}  = compPath-filler reflc λ i → x

transportCompose : ∀ {ℓ} {A B C : Set ℓ} → (pf1 : A ≡ B) → (pf2 : B ≡ C) → (a : A) → transport pf2 (transport pf1 a) ≡c transport (pf1 ∙ pf2) a
transportCompose pf1 pf2 a
  =
  JPath (λ y pf2 → transport pf2 (transport pf1 a) ≡c transport (pf1 ∙ pf2) a)
  (JPath
    (λ x pf1 →
      transportPath reflc (transportPath pf1 a) ≡c
      transportPath (compPath pf1 reflc) a)
    (transportRefl (transportPath reflc a) ∙ transportRefl a ∙ sym (transportRefl a) ∙ congPath (λ pf → transportPath pf a) reflCompose) pf1) pf2

path01eq : ∀ {ℓ} {A0 A1 : Set ℓ} (Aeq : A0 ≡c A1) → ∀ i → PathP (λ j → Aeq i ≡ Aeq j) (pathi0 Aeq i)  (pathi1 Aeq i)
path01eq Aeq i j = pathij Aeq i j

path01Transport : ∀ {ℓ} {A0 A1 : Set ℓ} (Aeq : A0 ≡c A1) → ∀ i (a :  Aeq i) → PathP (λ i → Aeq i) (transport (pathi0 Aeq i) a  ) (transport (pathi1 Aeq i) a)
path01Transport Aeq i a j = transportPath (pathij Aeq i j) a

-- funDomTrans : ∀ A0 A1 (Aeq : A0 ≡c A1) (B : ∀ {i} →  Aeq i → Set) → ((a : Aeq i0) → B {i0} a) ≡c

-- extP : ∀ {A0 A1 : Set} (Aeq : A0 ≡c A1) {B : ∀ {i} →  Aeq i → Set} → (f : (a : Aeq i0) → B {i0} a ) (g : (a : Aeq i1) → B {i1} a)
--   → (∀ {a0 : A0} {a1 : A1} (eqq : PathP (λ i → Aeq i) a0 a1) → PathP (λ i → B {i} (eqq i)) (f (eqq i0)) (g (eqq i1)))
--   → PathP (λ i → (a : Aeq i) → B {i} a ) f g
-- extP Aeq {B = B} f g pf = {!!}
--   where
    -- pth : PathP (λ j → B {i = j} (transport (pathij Aeq i j) a)) (f (transportPath (pathij Aeq i i0) a)) (g (transportPath (pathij Aeq i i1) a))
    -- pth = pf (path01Transport (λ i₁ → Aeq i₁) i a)

compPathPEx : ∀ {ℓ} (A : I → Set ℓ) (x : A i0) (y : A i1) (B_i1 : Set ℓ) (B : (A i1) ≡ B_i1) {z : B i1}
            → PathP A x y → PathP (λ i → B i) y z → PathP (λ j → ((λ i → A i) ∙ B) j) x z
compPathPEx A x y B_i1 B p q i =
  comp (λ j → compPath-filler (λ i → A i) B j i)
       (λ j → λ { (i = i0) → x ;
                  (i = i1) → q j })
       (p i)


transpFunLemma : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') (f : (a : A) → P a ) {x y} (pf : x ≡c y)
  → transport (cong P pf) (f x) ≡c (f y)
transpFunLemma P f {y = y} pf =
  (JPath {x = y} (λ z zpf → transport (cong P (sym zpf)) (f z) ≡c transport refl (f y)) refl (sym pf)) ∙ transportRefl (f _)



subLemma : ∀ {ℓ ℓ'} {A : Set ℓ} (P : A → Set ℓ') (f : (a : A) → P a ) {x y} (pf : x ≡c y)
  → subst P pf (f x) ≡c (f  y)
subLemma P f pf = transpFunLemma P f pf

funExtI : ∀ {ℓ} {f g : I → Set ℓ}
  → (∀ i → f i ≡c g i)
  → f ≡c g
funExtI p i x = p x i

pathTransport : ∀ {P : I → Set} {A : Set} {x : A} {eqA : A ≡c P i0} {y : P i1}
  → PathP (λ i → (eqA ∙ (λ j → P j)) i) x y
  → PathP P (transport eqA x) y
pathTransport pth = toPathP (symPath (transportComposite _ _ _) ∙ fromPathP pth)

compPathTransport : ∀ {P : I → Set} {A : Set} {x : A} {eqA : A ≡c P i0} {y : P i1}
  → {z : eqA i1}
  → PathP (λ z₁ → eqA z₁) x z
  → PathP P z y
  → PathP P (transport eqA x) y
compPathTransport pxz pzy = toPathP (symPath (transportComposite _ _ _) ∙ fromPathP (compPathP pxz pzy))

data Erase {ℓ} (A : Set ℓ) : Prop ℓ where
  erase : A → Erase A



-- compPathPGoal {P = P} {x = x} {z = z} {Y = Y} {y} eqxy eqyz pxy pyz =
--   let
--     cmp = compPathP pxy pyz
--   in transport (cong₂ {A = I → Set} {B = λ P → (P i0 × P i1)} (λ P (x , z) → PathP P x z) (funExtI (λ j → {!P i!})) λ _ → (x , z)) cmp
