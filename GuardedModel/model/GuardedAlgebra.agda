{-# OPTIONS --cubical --guarded #-}
module GuardedAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

-- record Approxable {ℓ} (A : Set ℓ) : Set ℓ where
--   field
--     default : A

-- open Approxable {{...}} public

record GuardedAlgebra : Typeω where
  field
    ▹_ : ∀ {l} → Set l → Set l
    ▸_ : ∀ {l} → ▹ Set l → Set l

    next : ∀ {ℓ} {A : Set ℓ} → A → ▹ A
    _⊛_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → ▹ (A → B) → ▹ A → ▹ B
    dfix : ∀ {l} {A : Set l} → (▹ A → A) → ▹ A
    pfix : ∀ {l} {A : Set l} (f : ▹ A → A) → dfix f ≡ (next (f (dfix f)))

  map▹ : ∀  {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (f : A → B) → ▹ A → ▹ B
  map▹ f x = (next f) ⊛ x

  fix : ∀ {l} {A : Set l} → (▹ A → A) → A
  fix f = f (dfix f)


  field
    hollowEq : ∀ {l}  {f : ▹ Set l → Set l} → ▸ dfix f ≡ ▹ fix f

  tyfix : ∀ {l} → (Set l → Set l) → Set l
  tyfix F = fix (λ x → F (▸ x))

  löb : ∀ {l} {A : Set l} → (f : ▹ A → A) → fix f ≡ f (next (fix f))
  löb f = cong f (pfix f)

  tylöb : ∀ {l} (F : Set l → Set l) → tyfix F ≡ F (▹ (tyfix F))
  tylöb F = cong F hollowEq

  field
    Dep▸ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} → ((x : A) → B x) → (x : ▹ A) → ▸ map▹ B x

    -- Lift monad and operations
    L : ∀ {ℓ} → Set ℓ → Set ℓ
    -- We take a "default" value for θ
    -- because for the approximate version of this, we need to give ⁇ as the default
    -- but if it's not a paramter, we run into mutual-defn issues
    -- TODO: Better to just make everything one giant mutual defn?
    θL : ∀ {ℓ} {A : Set ℓ} → A → ▹ (L A) → L A

open GuardedAlgebra {{...}} public
