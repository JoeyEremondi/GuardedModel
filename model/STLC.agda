{-# OPTIONS --cubical --guarded --rewriting #-}

open import GuardedModality
open import Util
open import Cubical.Foundations.Prelude
open import LiftingMonad
open import Level
open import Cubical.Data.Prod
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Empty




data Tipe : Set where
  _⟶_ : Tipe → Tipe → Tipe
  U : Tipe


data AstF (Self : Set) : Set where
  Var : (x : Self) →  AstF Self
  App : AstF Self → AstF Self → AstF Self
  Lam : Tipe → (Self → AstF Self) → AstF Self
  Unit : AstF Self


AST : Set
AST = tyfix AstF



infixr 0 _⊢_
_⊢_ : Set → Set → Set
a ⊢ b = a → b

data HasType (V : ▹ (AST → Tipe → Set)) :  AST → Tipe → Set where

  [Var] : ∀ {x τ} →
    ▸ (V ⊛ transport hollowEq x ⊛ next τ)      ->
    ----------------------------------
    HasType V (Var x) τ

  [Lam] : ∀ {t τ₁ τ₂} →
    ( (x : ▸ dfix _) →
    (▸ (V ⊛ transport hollowEq x ⊛ next τ₁)) ⊢ HasType V (t x) τ₂) →
    --------------------------------------
    HasType V (Lam τ₁ t)  (τ₁ ⟶ τ₂)

  [App] : ∀ {t₀ t₁ τ₁ τ₂} →
    HasType V t₀ (τ₁ ⟶ τ₂)    ->
    HasType V t₁ τ₁            ->
    --------------------------------------------
    HasType V (App t₀ t₁) τ₂

  [Unit] :
  -----------------------------
    HasType V Unit U

_⦂_ : AST → Tipe → Set
_⦂_ = fix HasType


id : AST
id = Lam U (λ x → Var x)

idType : id ⦂ (U ⟶ U)
idType = [Lam] (λ x xTy → [Var] xTy)

unitApp : AST
unitApp = App id Unit

unitAppTy : unitApp ⦂ U
unitAppTy = [App] idType [Unit]


data _↝_ : AST → AST → Set where
  [β] : ∀ {t1 t2 τ} →
    ------------------------------
    App (Lam τ t1) t2 ↝ t1 (transport⁻ hollowEq (next t2))

  [nextβ] : ∀ {t1 t2 τ} →
    Var (transport⁻ hollowEq (next (App (Lam τ t1) t2))) ↝ t1 (transport⁻ hollowEq (next t2))

open import Cubical.HITs.SetQuotients

Term : Set
Term = AST / _↝_


_ℛ_ : Term  → Tipe → Set
t ℛ (τ ⟶ τ₁) =  Σ[ f ∈ _ ]( (t ≡ [ Lam τ f ]) × ((x : AST) → [ x ] ℛ τ → [ f (transport⁻ hollowEq (next x))  ] ℛ τ₁)  )
t ℛ U = t ≡ [ Unit ]

soundness : ∀ t τ → t ⦂ τ → ([ t ] ℛ τ)
soundness .(Var _) τ ([Var] x) = {!!}
soundness .(App _ _) τ ([App] 𝒟 𝒟₁)  = {!!}
soundness (Lam _ t) .(_ ⟶ _) ([Lam] 𝒟) = t , (refl , {!!})
soundness .Unit .U [Unit] = refl
