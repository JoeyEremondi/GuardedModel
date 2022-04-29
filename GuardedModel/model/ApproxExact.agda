{-# OPTIONS --cubical --guarded #-}

module ApproxExact where

open import GuardedAlgebra using (GuardedAlgebra)
import GuardedModality as G
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude

data Æ : Set where
  Approx Exact : Æ

data IsExact : Æ → Prop where
  instance isExact : IsExact Exact


data LÆ {ℓ} {{æ : Æ}} (A : Set ℓ) : Set ℓ where
  Now : A → LÆ A
  Later : {{_ : IsExact æ}} → G.▹ (LÆ A) → LÆ A
  Extract : ∀ {{_ : IsExact æ}} x → Later (G.next x) ≡ x

pure : ∀ {ℓ} {A : Set ℓ} {{_ : Æ}} → A → LÆ A
pure = Now


_>>=_ :
  ∀ {{_ : Æ}} {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
  → LÆ A → (A → LÆ B) → LÆ B
Now a >>= f = f a
Later x >>= f = Later λ tic → x tic >>= f
_>>=_ {A = A} (Extract x i) f = path {a = x} i
  where
    path : ∀ {a : LÆ A} → Later (G.next (a >>= f)) ≡ a >>= f
    path {a = a} = Extract (a >>= f)


_>>_ : ∀ {{_ : Æ}} {ℓ₁ ℓ₂} { A : Set ℓ₁ } {B : Set ℓ₂} → LÆ A → (A → LÆ B) → LÆ Unit
_>>_ ma f = ma >>= λ a → f a >>= λ _ → pure tt

_<*>_ : ∀ {{_ : Æ}} {ℓ₁ ℓ₂} { A : Set ℓ₁ } {B : Set ℓ₂} → LÆ (A → B) → LÆ A → LÆ B
mf <*> mx = do
   f ← mf
   x ← mx
   pure (f x)

fromNow : ∀ {ℓ} {A : Set ℓ} → LÆ {{Approx}} A → A
fromNow (Now x) = x


untic : ∀ {ℓ} {X : Set ℓ} → G.Tick → LÆ {{Exact}} X → X
untic tic (Now x) = x
untic tic (Later x) = untic tic (x tic)
untic tic (Extract x i) = untic tic x

liftFun : ∀ {{æ : Æ}} {ℓ₁} {ℓ₂} {A : Set ℓ₁} { B : Set ℓ₂ } → (A → LÆ B) → LÆ (A → B)
liftFun ⦃ Approx ⦄ f = Now (λ x → fromNow (f x))
liftFun ⦃ Exact ⦄ {A = A} {B}  f = Later λ tic → Now λ x → untic tic (f x)

liftFunDep : ∀ {{æ : Æ}} {ℓ₁} {ℓ₂} {A : Set ℓ₁} { B : A → Set ℓ₂ } → ((x : A) → LÆ (B x)) → LÆ ((x : A) → B x)
liftFunDep ⦃ Approx ⦄ f = Now (λ x → fromNow (f x))
liftFunDep ⦃ Exact ⦄ {A = A} {B}  f = Later λ tic → Now λ x → untic tic (f x)

unliftFunDep : ∀ {{æ : Æ}} {ℓ₁} {ℓ₂} {A : Set ℓ₁} { B : A → Set ℓ₂ } → LÆ ((x : A) → B x) → (x : A) → LÆ (B x)
unliftFunDep mf a = do
  f ← mf
  pure (f a)

uptoTermination : ∀ {{æ : Æ}} {ℓ}  {A : Set ℓ} → (P : A → Set ℓ) → LÆ {{æ}} A → Set ℓ
uptoTermination {A = A} P x = Σ[ y ∈ A ]((x ≡ Now y) × P y)



instance
  approxExact : {{_ : Æ}} → GuardedAlgebra
  GuardedAlgebra.▹ approxExact ⦃ Approx ⦄ = λ _ → Unit*
  GuardedAlgebra.▸ approxExact ⦃ Approx ⦄ = λ _ → Unit*
  GuardedAlgebra.next (approxExact ⦃ Approx ⦄) = λ _ → tt*
  GuardedAlgebra._⊛_ (approxExact ⦃ Approx ⦄) = λ _ _ → tt*
  GuardedAlgebra.dfix (approxExact ⦃ Approx ⦄) = λ _ → tt*
  GuardedAlgebra.pfix (approxExact ⦃ Approx ⦄) = λ _ → refl
  GuardedAlgebra.hollowEq (approxExact ⦃ Approx ⦄) = refl
  GuardedAlgebra.Dep▸ (approxExact ⦃ Approx ⦄) = λ _ _ → tt*
  GuardedAlgebra.▹ approxExact ⦃ Exact ⦄ = λ A → G.▹ A
  GuardedAlgebra.▸ approxExact ⦃ Exact ⦄ = λ ▹A → G.▸ ▹A
  GuardedAlgebra.next (approxExact ⦃ Exact ⦄) = G.next
  GuardedAlgebra._⊛_ (approxExact ⦃ Exact ⦄) = G._⊛_
  GuardedAlgebra.dfix (approxExact ⦃ Exact ⦄) = G.dfix
  GuardedAlgebra.pfix (approxExact ⦃ Exact ⦄) = G.pfix
  GuardedAlgebra.hollowEq (approxExact ⦃ Exact ⦄) = G.hollowEq
  GuardedAlgebra.Dep▸ (approxExact ⦃ Exact ⦄) = λ f x tic → f (x tic)
  GuardedAlgebra.L (approxExact ⦃ æ ⦄) A = LÆ {{æ}} A
  GuardedAlgebra.θL (approxExact ⦃ Approx ⦄) a x = Now a
  GuardedAlgebra.θL (approxExact ⦃ Exact ⦄) a x = Later x

open import GuardedAlgebra


-- LFix : ∀ {{_ : Æ}} {ℓ} {A : Set ℓ} {{apprx : Approxable A}}
--   → (LÆ A → LÆ  A) → LÆ  A
-- LFix {{Approx}} f = f (Now default)
-- LFix {{Exact}} f = G.fix (λ x → f (Later x))


-- LFix' : ∀ {{_ : Æ}} {ℓ} {A : Set ℓ} {{apprx : Approxable A}}
--   → (A → LÆ  A) → LÆ  A
-- LFix' f = LFix (_>>= f)



-- LFixFun : ∀ {{_ : Æ}} {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} {{appr : ∀ {a} → Approxable (B a)}} →
--   (f : ((a : A) → LÆ (B a)) → (a : A) → LÆ  (B a)) → (a : A) → LÆ  (B a)
-- LFixFun {A = A} {{appr}} f =
--   unliftFunDep
--     (LFix {{_}} {{record { default = λ a → Approxable.default appr  }}}
--     λ self → liftFunDep (λ a → f (unliftFunDep self) a))
