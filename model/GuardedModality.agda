{-# OPTIONS --cubical --guarded #-}
module GuardedModality where

import GuardedAlgebra as Alg
open import Agda.Primitive
open import Agda.Primitive.Cubical renaming (itIsOne to 1=1)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS)
open import Cubical.Foundations.Prelude using (cong ; transport ; sym ; _∙_)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

private
  variable
    l : Level
    A B : Set l

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU



▹_ : ∀ {l} → Set l → Set l
▹_ A = (@tick x : Tick) -> A

▸_ : ∀ {l} → ▹ Set l → Set l
▸ A = (@tick x : Tick) → A x

next : A → ▹ A
next x _ = x

infixl 100 _⊛_
_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x a = f a (x a)

map▹ : (f : A → B) → ▹ A → ▹ B
map▹ f x α = f (x α)

mapNext : (f : A → B) → (a : A) → (map▹ f (next a)) ≡ next (f a)
mapNext f a α i = f a

transpLater : ∀ (A : I → ▹ Set) → ▸ (A i0) → ▸ (A i1)
transpLater A u0 a = primTransp (\ i → A i a) i0 (u0 a)

transpLater-prim : (A : I → ▹ Set) → (x : ▸ (A i0)) → ▸ (A i1)
transpLater-prim A x = primTransp (\ i → ▸ (A i)) i0 x

transpLater-test : ∀ (A : I → ▹ Set) → (x : ▸ (A i0)) → transpLater-prim A x ≡ transpLater A x
transpLater-test A x = \ _ → transpLater-prim A x


hcompLater-prim : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater-prim A φ u u0 a = primHComp (\ { i (φ = i1) → u i 1=1 a }) (outS u0 a)


hcompLater : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
hcompLater A φ u u0 = primHComp (\ { i (φ = i1) → u i 1=1 }) (outS u0)

hcompLater-test : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → hcompLater A φ u u0 ≡ hcompLater-prim A φ u u0
hcompLater-test A φ u x = \ _ → hcompLater-prim A φ u x

ap : ∀ {A B : Set} (f : A → B) → ∀ {x y} → x ≡ y → f x ≡ f y
ap f eq = \ i → f (eq i)

_$>_ : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ x → f x ≡ g x
eq $> x = \ i → eq i x

later-ext : ∀ {l} {A : Set l} → {f g : ▹ A} → (▸ \ α → f α ≡ g α) → f ≡ g
later-ext eq = \ i α → eq α i

later-ext' : ∀ {l} {A : ▹ Set l} → {f g : ▸ A} → (▸ \ α → f α ≡ g α) → f ≡ g
later-ext' eq = \ i α → eq α i

later-extSwap : ∀ {l} {A : ▹ Set l} {B : Set l} → (▸ \ α → A α ≡ B) → ▸ A ≡ ▹ B
later-extSwap eq i = (x : Tick) → eq x i

postulate
  dfix : ∀ {l} {A : Set l} → (▹ A → A) → ▹ A
  pfix : ∀ {l} {A : Set l} (f : ▹ A → A) → dfix f ≡ (\ _ → f (dfix f))

pfix' : ∀ {l} {A : Set l} (f : ▹ A → A) → ▸ \ α → dfix f α ≡ f (dfix f)
pfix' f α i = pfix f i α

fix : ∀ {l} {A : Set l} → (▹ A → A) → A
fix f = f (dfix f)

lob : ∀ {l} {A : Set l} → (f : ▹  A → A) → fix f ≡ f (next (fix f))
lob f = cong f (pfix f)

unhollow : ∀ {l}  {f : ▹ Set l → Set l} → ▹ (fix f) → ▸ dfix f
unhollow {f = f} x tic = transport⁻ (pfix' f tic) (x tic)

hollow : ∀ {l}  {f : ▹ Set l → Set l} → ▸ dfix f → ▹ fix f
hollow  {f = f} x tic = transport (pfix' f tic) (x tic)

hollowEq : ∀ {l}  {f : ▹ Set l → Set l} → ▸ dfix f ≡ ▹ fix f
hollowEq {f = f} i = (tic : Tick) → pfix' f tic i

tyfix : ∀ {l} → (Set l → Set l) → Set l
tyfix F = fix λ x → F (▸ x)

tylob : ∀ {l} (F : Set l → Set l) → tyfix F ≡ F (▹ (tyfix F))
tylob F = cong F hollowEq


-- data LiftM {ℓ} (A : Set ℓ) : Set ℓ where
--   Now : A → LiftM A
--   Later : ▹ (LiftM A) → LiftM A
--   Extract : ∀ {x} → Later (next x) ≡ x

-- -- We don't need to worry about the HIT stuff when using do notation:
-- -- bind always respects the needed equality
-- _>>=_ :
--   ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
--   → LiftM A → (A → LiftM B) → LiftM B
-- Now a >>= f = f a
-- Later x >>= f = Later λ tic → x tic >>= f
-- _>>=_ {A = A} (Extract {x = x} i) f = path {a = x} i
--   where
--     path : ∀ {a : LiftM A} → Later (next (a >>= f)) ≡ a >>= f
--     path = Extract



-- instance
--   guardedModality : Alg.GuardedAlgebra
--   Alg.GuardedAlgebra.▹ guardedModality = ▹_
--   Alg.GuardedAlgebra.▸ guardedModality = ▸_
--   Alg.GuardedAlgebra.next guardedModality = next
--   Alg.GuardedAlgebra._⊛_ guardedModality = _⊛_
--   Alg.GuardedAlgebra.dfix guardedModality = dfix
--   Alg.GuardedAlgebra.pfix guardedModality = pfix
--   Alg.GuardedAlgebra.Dep▸ guardedModality = λ f x tic → f (x tic)
--   Alg.GuardedAlgebra.hollowEq guardedModality = hollowEq
--   Alg.GuardedAlgebra.L guardedModality = LiftM
--   Alg.GuardedAlgebra.θL guardedModality _  = Later
--   Alg.GuardedAlgebra.pure guardedModality  = Now
--   Alg.GuardedAlgebra._>>=_ guardedModality = _>>=_
