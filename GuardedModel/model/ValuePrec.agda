{-# OPTIONS --cubical --guarded #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Equality
open import Inductives
open import GuardedAlgebra
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude

open import ApproxExact
open import InductiveCodes
open import CodeSize
open import WMuEq

module ValuePrec {{_ : DataTypes}} {{_ : DataGerms}} {{_ : InductiveCodes}} {{_ : DataGermsSmaller}} where

open import Code
open import Head
open import Util
open import Ord
-- open Ord ℂ El ℧ C𝟙 refl


open import Germ


record SizedPrec (cSize : Ord) : Set1 where
  field
    o⊑c : ∀ {{_ : Æ}} {ℓ}
      → (c₁ c₂ : ℂ ℓ)
      → {@(tactic default (reflp {A = Ord} {cSize})) pf : omax (codeSize c₁) (codeSize c₂) ≡p cSize}
      → Set
    o⊑v : ∀ {{_ : Æ}} {ℓ} {c₁ c₂ : ℂ ℓ} {pf}
      → El c₁
      → El c₂
      → o⊑c c₁ c₂ {pf}
      → Set

open SizedPrec

record PrecModule (cSize : Ord) : Set1 where
  field
    self : ∀ {size' : Ord} → size' <o cSize → SizedPrec size'
  interleaved mutual
    data _⊑_ {{_ : Æ}} {ℓ}
      : (c₁ c₂ : ℂ ℓ)
      → Set
    data _⊑_⦂_  {{_ : Æ}} {ℓ}
      : {c₁ c₂ : ℂ ℓ}
      → El c₁
      → El c₂
      → c₁ ⊑ c₂
      → Set
    data _ where
      ⊑⁇ : ∀ {c} → c ⊑ C⁇
  sizedPrec : SizedPrec cSize
  sizedPrec = record { o⊑c = λ c₁ c₂ {pf} → c₁ ⊑ c₂  ; o⊑v = λ v1 v2 c⊑ → v1 ⊑ v2 ⦂ c⊑ }
