module GuardedModality where

import GuardedAlgebra as Alg
open import Agda.Primitive
open import ErasedCompatiblePath
open import Relation.Binary.PropositionalEquality
-- open import Agda.Primitive.Cubical renaming (itIsOne to 1=1)
-- open import Agda.Builtin.Cubical.Path
-- open import Agda.Builtin.Cubical.Sub renaming (Sub to _[_↦_]; primSubOut to outS)
-- open import Cubical.Foundations.Prelude using (cong ; transport ; sym ; _∙_)
-- open import Cubical.Foundations.Transport
-- open import Cubical.Foundations.Univalence
-- open import Cubical.Foundations.Isomorphism

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

mapNextC : (f : A → B) → (a : A) → (map▹ f (next a)) ≡c next (f a)
mapNextC f a α i = f a

transpLater : ∀ (A : I → ▹ Set) → ▸ (A i0) → ▸ (A i1)
transpLater A u0 a = transp (\ i → A i a) i0 (u0 a)

transpLater-prim : (A : I → ▹ Set) → (x : ▸ (A i0)) → ▸ (A i1)
transpLater-prim A x = transp (\ i → ▸ (A i)) i0 x

transpLater-test : ∀ (A : I → ▹ Set) → (x : ▸ (A i0)) → transpLater-prim A x ≡c transpLater A x
transpLater-test A x = \ _ → transpLater-prim A x


-- hcompLater-prim : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
-- hcompLater-prim A φ u u0 a = primHComp (\ { i (φ = i1) → u i 1=1 a }) (outS u0 a)


-- hcompLater : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → ▸ A
-- hcompLater A φ u u0 = primHComp (\ { i (φ = i1) → u i 1=1 }) (outS u0)

-- hcompLater-test : ∀ (A : ▹ Set) φ (u : I → Partial φ (▸ A)) → (u0 : (▸ A) [ φ ↦ u i0 ]) → hcompLater A φ u u0 ≡ hcompLater-prim A φ u u0
-- hcompLater-test A φ u x = \ _ → hcompLater-prim A φ u x

ap : ∀ {A B : Set} (f : A → B) → ∀ {x y} → x ≡ y → f x ≡ f y
ap f eq = ctop (\ i → f ((ptoc eq) i))

_$>_ : ∀ {A B : Set} {f g : A → B} → f ≡ g → ∀ x → f x ≡ g x
eq $> x = ctop \ i → (ptoc eq) i x

later-ext : ∀ {l} {A : Set l} → {f g : ▹ A} → (▸ \ α → f α ≡ g α) → f ≡ g
later-ext eq = ctop \ i α → ptoc (eq α) i

later-ext' : ∀ {l} {A : ▹ Set l} → {f g : ▸ A} → (▸ \ α → f α ≡ g α) → f ≡ g
later-ext' eq = ctop \ i α → (ptoc (eq α)) i

later-extSwap : ∀ {l} {A : ▹ Set l} {B : Set l} → (▸ \ α → A α ≡ B) → ▸ A ≡ ▹ B
later-extSwap eq = ctop λ i → (@tick x : Tick) → ptoc (eq x) i

postulate
  dfix : ∀ {l} {A : Set l} → (▹ A → A) → ▹ A
  pfixc : ∀ {l} {A : Set l} (f : ▹ A → A) → dfix f ≡c (\ _ → f (dfix f))

pfix : ∀ {l} {A : Set l} (f : ▹ A → A) → dfix f ≡ (\ _ → f (dfix f))
pfix f = ctop (pfixc f)


pfix' : ∀ {l} {A : Set l} (f : ▹ A → A) → ▸ \ α → dfix f α ≡ f (dfix f)
pfix' f α = ctop λ i → ptoc (pfix f) i α

fix : ∀ {l} {A : Set l} → (▹ A → A) → A
fix f = f (dfix f)

lob : ∀ {l} {A : Set l} → (f : ▹  A → A) → fix f ≡ f (next (fix f))
lob f = cong f (ctop (pfixc f)) -- cong f (pfixc f)

unhollow : ∀ {l}  {f : ▹ Set l → Set l} → ▹ (fix f) → ▸ dfix f
unhollow {f = f} x tic = transportc⁻ (ptoc (pfix' f tic)) (x tic)

hollow : ∀ {l}  {f : ▹ Set l → Set l} → ▸ dfix f → ▹ fix f
hollow  {f = f} x tic = transportc  (ptoc (pfix' f tic)) (x tic)

hollowEq' : ∀ {l}  {f : ▹ Set l → Set l} → ▸ dfix f ≡c ▹ fix f
hollowEq' {f = f} i = (@tick tic : Tick) → (ptoc (pfix' f tic)) i


hollowEq : ∀ {l}  {f : ▹ Set l → Set l} → ▸ dfix f ≡ ▹ fix f
hollowEq {f = f} = ctop hollowEq'

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
--   Alg.GuardedAlgebra.pfixc guardedModality = pfixc
--   Alg.GuardedAlgebra.Dep▸ guardedModality = λ f x tic → f (x tic)
--   Alg.GuardedAlgebra.hollowEq guardedModality = hollowEq
--   Alg.GuardedAlgebra.L guardedModality = LiftM
--   Alg.GuardedAlgebra.θL guardedModality _  = Later
--   Alg.GuardedAlgebra.pure guardedModality  = Now
--   Alg.GuardedAlgebra._>>=_ guardedModality = _>>=_
