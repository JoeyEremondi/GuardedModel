{-# OPTIONS --cubical --guarded #-}

module ApproxExact where

open import GuardedAlgebra using (GuardedAlgebra)
import GuardedModality as G
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Data.Equality

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

data _≤Æ_ : Æ → Æ → Set where
  ≤æRefl : Exact ≤Æ Exact
  instance ≤æBot : ∀ {æ} → Approx ≤Æ æ

instance exactTrans : ∀ {æ1 æ2} → {{_ : æ1 ≤Æ æ2}} → {{_ : IsExact æ1}} → IsExact æ2
exactTrans {Exact} {Exact} = isExact

instance exactRefl : ∀ {æ} → æ ≤Æ æ
exactRefl {Approx} = ≤æBot
exactRefl {Exact} = ≤æRefl

_>>=_ :
  ∀ {æA} {æB} {{_ : æA ≤Æ æB}} {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
  → LÆ {{æ = æA}} A → (A → LÆ {{æ = æB}} B) → LÆ {{æ = æB}} B
Now a >>= f = f a
Later x >>= f = Later  λ tic → x tic >>= f
_>>=_ {æA = æA} {æB} {A = A} (Extract x i) f = path {a = x} i
  where
    path : {a : LÆ {{_}} A} → Later {{æ = æB}} (G.next (a >>= f)) ≡ a >>= f
    path {a = a} = Extract {{æ = æB}} (a >>= f)


_>>_ :
  ∀ {æA} {æB} {{_ : æA ≤Æ æB}} {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
  → LÆ {{æ = æA}} A → (A → LÆ {{æ = æB}} B) → LÆ {{æ = æB}} Unit
_>>_ {æB = æB} ma f = ma >>= λ a → f a >>= λ _ → pure {{æB}} tt

_<*>_ : ∀ {{_ : Æ}} {ℓ₁ ℓ₂} { A : Set ℓ₁ } {B : Set ℓ₂} → LÆ (A → B) → LÆ A → LÆ B
mf <*> mx = do
   f ← mf
   x ← mx
   pure (f x)

_<$>_ : ∀ {{_ : Æ}} {ℓ₁ ℓ₂} { A : Set ℓ₁ } {B : Set ℓ₂} → (A → B) → LÆ A → LÆ B
f <$> mx = do
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

data GUnit {ℓ} : Set ℓ where
  U⁇ U℧ : GUnit


instance
  approxExact : {{_ : Æ}} → GuardedAlgebra
  GuardedAlgebra.▹ approxExact ⦃ Approx ⦄ = λ _ → GUnit
  GuardedAlgebra.▸ approxExact ⦃ Approx ⦄ = λ _ → GUnit
  GuardedAlgebra.next (approxExact ⦃ Approx ⦄) = λ x → U⁇
  GuardedAlgebra._⊛_ (approxExact ⦃ Approx ⦄) = λ { f U⁇ → U⁇ ; f U℧ → U℧}
  GuardedAlgebra.dfix (approxExact ⦃ Approx ⦄) = λ x → U⁇
  GuardedAlgebra.pfix (approxExact ⦃ Approx ⦄) = λ x → refl
  GuardedAlgebra.hollowEq (approxExact ⦃ Approx ⦄) = refl
  GuardedAlgebra.Dep▸ (approxExact ⦃ Approx ⦄) = λ { f U⁇ → U⁇ ; f U℧ → U℧}
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

-- If we're in approximate mode, this is just an approximate version of a T
-- In exact mode, it's a pair with an approximate and exact version of a T
Approxed : ∀ (T : {{_ : Æ }} → Set) → {{æ : Æ}} → Set
Approxed T ⦃ Approx ⦄ = T {{Approx}}
Approxed T ⦃ Exact ⦄ = T {{Approx}} × T {{Exact}}
--Get the approximate version stored in an Approxed value
approx : ∀ {T : {{_ : Æ }} → Set} → {{æ : Æ}} → Approxed T {{æ}} → T {{Approx}}
approx ⦃ æ = Approx ⦄ x = x
approx ⦃ æ = Exact ⦄ x = fst x

exact : ∀ {T : {{_ : Æ }} → Set} → {{æ : Æ}} → Approxed (λ {{æ : Æ}} → T {{æ}}) {{æ}}  → T {{æ}}
exact ⦃ æ = Approx ⦄ x = x
exact ⦃ æ = Exact ⦄ x = snd x

withApprox : ∀ {{æRet : Æ}} {T : {{æ : Æ }}  → Set} → (f : ∀ (æ : Æ) →  T {{æ}} )  → Approxed T {{æRet}}
withApprox {{Approx}} f   = f Approx
withApprox {{Exact}} f  = f Approx  , f Exact


withApproxL : ∀ {{æRet : Æ}} {T : {{æ : Æ }}  → Set} → (f : ∀ (æ : Æ) → LÆ {{æ}} (T {{æ}}) )  → LÆ {{æRet}} (Approxed T {{æRet}})
withApproxL {{Approx}} f   = f Approx
withApproxL {{Exact}} f  = do
  a ← f Approx
  e ← f Exact
  pure {{Exact}} (a , e)

withApproxL' : ∀ {{æRet : Æ}} {T : {{æ : Æ }}  → Set} → (f : ∀ (æ : Æ) (conv : Approxed T {{æRet}} → Approxed T {{æ}}) → LÆ {{æ}} (T {{æ}}) )  → LÆ {{æRet}} (Approxed T {{æRet}})
withApproxL' {{Approx}} f   = f Approx λ x → x
withApproxL' {{Exact}} {T = T} f  = do
  a ← f Approx (approx {T = T} {{Exact}} )
  e ← f Exact λ x → x
  pure {{Exact}} (a , e)

-- pairWithApprox : ∀ {T : {{_ : Æ }} → Set} → {{æ : Æ}} → T {{Approx}} → T {{æ}} → Approxed T {{æ}}
-- pairWithApprox ⦃ æ = Approx ⦄ a e = a
-- pairWithApprox ⦃ æ = Exact ⦄ a e = a , e

-- approxPairEq : ∀ {T : {{_ : Æ }} → Set} → {{æ : Æ}} → (a : T {{Approx}}) → (e : T {{æ}}) →
--   approx (pairWithApprox {T} a e) ≡p a
-- approxPairEq ⦃ æ = Approx ⦄ _ _ = reflp
-- approxPairEq ⦃ æ = Exact ⦄ _ _ = reflp


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
