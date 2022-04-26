

open import Source.SyntaxParams
module Source.Test {{_ : Language}} {{_ : Inductives}} where

open import Cubical.Data.Nat
open import Cubical.Data.Equality hiding (Sub)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import DecPEq
open import Cubical.Data.List

open import Syntax

postulate
  AST : Set
  -- _•_ :  ABT → (ℕ → ABT) → ℕ → ABT
  Op : Set
  sig : Op → List Sig


open Syntax.OpSig Op sig public


Name = ℕ

data Sub : Set where
  wrapSub : (Name → ABT) -> Sub

postulate
  ABT→AST : ABT → AST
  abtSub : Sub → Name → ABT
  Asub-η : ∀ σ x → (⟪ σ ⟫ (` 0) • (↑ 1 ⨟ σ)) x ≡ (σ) x

[]-sub-eta : ∀ {x t⃗} ->
  ABT→AST
      ((abtSub t⃗ 0 • (λ x₁ → abtSub t⃗ (suc x₁))  ) x)
      ≡p ABT→AST (abtSub t⃗ x)

[]-sub-eta {x} {t⃗} =  pCong ABT→AST (Asub-η (abtSub t⃗) x)

{-# REWRITE []-sub-eta #-}
