{-# OPTIONS --cubical --guarded  #-}
open import Source.SyntaxParams

open import GuardedAlgebra
open import Inductives
open import Source.Tele {{CastCalc}}

module Model {{_ : Inductives}} {{_ : GuardedAlgebra}} {{_ : Datatypes}} {{ _ : IndParams  }} where

open import Source.Syntax {{CastCalc}}
open import Source.Types
open import Source.Sub
open import Cubical.Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Prod
open import Source.Redex
open import Cubical.Foundations.Prelude

open import Code

Σℂ = Σ ℕ ℂ

pairℂ : ∀ {i} → ℂ i → Σℂ
pairℂ {i} c =  (i , c)

data ℂEnv : ℕ → Set
ℂSub : ∀ {n} → ℂEnv n → Set
ElApp : ∀ {n} {Δ : ℂEnv n} → (ℂSub Δ → Σℂ)  → ℂSub Δ → Type


data ℂEnv where
  ℂNil : ℂEnv 0
  ℂSnoc : ∀ {n} → (Δ : ℂEnv n) → (ℂSub Δ → Σℂ) → ℂEnv (suc n)

ℂSub ℂNil = Unit
ℂSub (ℂSnoc Δ cd) = Σ[ δ ∈ ℂSub Δ ] (ElApp cd δ)
ElApp cd δ with (i , c) ← cd δ = El {i} c

Under : ∀ {ℓ n} (Δ : ℂEnv n) (A :  ℂSub Δ → Set ℓ) → Set ℓ
Under Δ A = (δ : ℂSub Δ) → (A δ)

Under' : ∀ {ℓ n} (Δ : ℂEnv n) (A :  Set ℓ) → Set ℓ
Under' Δ A = Under Δ (λ _ → A)

underExt : ∀ {ℓ n} {A : Set ℓ} (Δ : ℂEnv n) (x : ℂSub Δ → Σℂ)  → Under' (ℂSnoc Δ x) A → Under Δ (λ δ → ElApp x δ →  A)
underExt Δ x u δ δx = u (δ , δx)

-- Allow us to use idiom brackets
--
infixl 5 _<*>_
pure : ∀ {ℓ n}  {Δ : ℂEnv n} {A :  Set ℓ} → A → Under Δ (λ _ → A)
pure a δ = a
_<*>_ : ∀ {ℓ₁} {ℓ₂} {n} {Δ : ℂEnv n} {A : Under' Δ (Set ℓ₁)} {B : Under Δ (λ δ →  A δ → Set ℓ₂)}
          → (f : Under Δ (λ δ → (x : A δ) → B δ x) ) →  (ax : Under Δ A) → Under Δ λ δ → B δ (ax δ)
(fm <*> xm) δ    = fm δ (xm δ)

[x⦂_] : ∀ {i n} {Δ : ℂEnv n} → Under' Δ (ℂ i) → Under'  Δ (Σℂ)
[x⦂ c ] δ = (_ , c δ)



data _&_⊢𝒯⟦_⟧by[_]≔_ {n} : ∀ {i} (Γ : Vec AST n) (Δ : ℂEnv n)  → (T : AST) →  (Γ ⊢ T ⇒[ OType 0 ] (SType i)) → (Under' Δ (ℂ i)) → Set


_&_⊢ℰ⟦_⟧by[_⦂_] : ∀ {n t T i}  → (Γ : Vec AST n) → (Δ : ℂEnv n) → {c : Under' Δ (ℂ i)}
  →  {𝒟 : Γ ⊢ T ⇒[ OType 0 ] (SType i)}
  →  AST → (Γ ⊢ t ⇐ T) → (Γ &  Δ ⊢𝒯⟦ T ⟧by[ 𝒟 ]≔ c)
  →  Under Δ (λ δ → El (c δ) )


data _&_⊢𝒯⟦_⟧by[_]≔_ where
  𝒯Type : ∀ {Γ Δ i} →
    ------------------------------
    Γ & Δ ⊢𝒯⟦ SType i ⟧by[ PSynthType Ty⇒ defeqRefl ]≔ pure (CType {suc i})

  𝒯Pi : ∀ {Γ} {Δ} {i j} {T₁} {T₂}
    {c₁ : Under' Δ (ℂ i)}
    {c₂ : Under' (ℂSnoc Δ [x⦂ c₁ ]) (ℂ j)} →
    (D₁ : Γ ⊢ T₁ ⇒[ OType 0 ] SType i) →
    (D₂ : (T₁ ∷ Γ) ⊢ T₂ ⇒[ OType 0 ] SType j) →
    (DC1 : Γ & Δ ⊢𝒯⟦ T₁ ⟧by[ D₁ ]≔ c₁) →
    --TODO need weakening
    (DC2 : (T₁ ∷ Γ) & (ℂSnoc Δ [x⦂ c₁ ]) ⊢𝒯⟦ T₂ ⟧by[ D₂ ]≔ c₂) →
    ----------------------------------------
    Γ & Δ ⊢𝒯⟦ [x⦂ T₁ ]⟶ T₂ ⟧by[ PSynthType (Pi⇒ D₁ D₂) defeqRefl ]≔ λ δ →
      CΠ {ℓ = max i j} (liftℂ {j = i} {k = max i j} left-≤-max  (c₁ δ)) λ x → liftℂ {j = j} {k = max i j} right-≤-max (c₂ (δ , transport (ElLiftℂ i (max i j) (left-≤-max)) x))

  𝒯Eq : ∀ {Γ Δ T i t₁ t₂ c}  →
    ( DT :  Γ ⊢ T ⇒[ OType 0 ] (SType i)) →
    (D1 : Γ ⊢ t₁ ⇐ T) →
    (D2 : Γ ⊢ t₂ ⇐ T) →
    (DC : Γ & Δ ⊢𝒯⟦ T ⟧by[ DT ]≔ c) →
    ------------------------------------
    Γ & Δ ⊢𝒯⟦ t₁ ≡[ T ] t₂ ⟧by[ PSynthType (Eq⇒ DT D1 D2) defeqRefl ]≔ (| (C≡ {i}) c (Γ & Δ ⊢ℰ⟦ t₁ ⟧by[ {!!} ⦂ {!!} ] ) (Γ & Δ ⊢ℰ⟦ t₂ ⟧by[ {!!} ⦂ {!!}  ]) |)
