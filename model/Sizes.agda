{-# OPTIONS --cubical --guarded --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import UnkGerm
open import InductiveCodes
open import Cubical.Data.Nat

open import Constructors

module Sizes {{_ : DataTypes}} {{_ : DataGerms}} {{_ : CodesForInductives }} where


open import Code
open import ApproxExact



open import Sizes.Size public
open import Sizes.MultiMax public
open import Sizes.NatLim public
open import Sizes.WellFounded public

import Sizes.CodeSize
import Sizes.ElSize

smallerCodeSize : ∀ {ℓ} {{inst : 0< ℓ}} → ℂ-1 (SmallerCodeAt ℓ) → Size
smallerCodeSize {suc ℓ}  = Sizes.CodeSize.codeSize smallerCodeSize


smallerElSize :  ∀ {{æ : Æ}} {ℓ} {{inst : 0< ℓ}} → (c : ℂ-1 (SmallerCodeAt ℓ)) → El-1 (SmallerCodeAt ℓ) c → Size
smallerElSize {suc ℓ} = Sizes.ElSize.elSize smallerCodeSize smallerElSize


module _ {ℓ} where
  open import Sizes.CodeSize {ℓ} smallerCodeSize public
  open import Sizes.ElSize {ℓ} smallerCodeSize smallerElSize public



codeSuc : ∀ {ℓ} (c : ℂ ℓ) → SZ <ₛ codeSize c
codeSuc C⁇ = ≤ₛ-sucMono ≤ₛ-Z
codeSuc C℧ =  ≤ₛ-sucMono  ≤ₛ-Z
codeSuc C𝟘 = ≤ₛ-sucMono  ≤ₛ-Z
codeSuc C𝟙 = ≤ₛ-sucMono ≤ₛ-Z
codeSuc Cℕ = ≤ₛ-sucMono ≤ₛ-Z
codeSuc CType = ≤ₛ-sucMono ≤ₛ-Z
codeSuc (CΠ c cod) = ≤ₛ-sucMono ≤ₛ-Z
codeSuc (CΣ c cod) = ≤ₛ-sucMono ≤ₛ-Z
codeSuc (C≡ c x y) = ≤ₛ-sucMono ≤ₛ-Z
codeSuc (Cμ tyCtor c D x) = ≤ₛ-sucMono ≤ₛ-Z
codeSuc {ℓ = suc ℓ} (CCumul c) = codeSuc {ℓ = ℓ} c

codeMaxL : ∀ {ℓ} (c : ℂ ℓ) → smax S1 (codeSize c) ≤ₛ codeSize c
codeMaxL C⁇ = smax-oneL -- ≤ₛ-sucMono smax-oneL
codeMaxL C℧ = smax-oneL
codeMaxL C𝟘 = smax-oneL
codeMaxL C𝟙 = smax-oneL
codeMaxL Cℕ = smax-oneL
codeMaxL CType = smax-oneL
codeMaxL (CΠ c cod) = smax-oneL
codeMaxL (CΣ c cod) = smax-oneL
codeMaxL (C≡ c x y) = smax-oneL
codeMaxL (Cμ tyCtor c D x) = smax-oneL
codeMaxL {ℓ = suc ℓ} (CCumul c) = codeMaxL c -- smax-oneL


codeMaxR : ∀ {ℓ} (c : ℂ ℓ) → smax (codeSize c) S1 ≤ₛ codeSize c
codeMaxR C⁇ = smax-oneR
codeMaxR C℧ = smax-oneR
codeMaxR C𝟘 = smax-oneR
codeMaxR C𝟙 = smax-oneR
codeMaxR Cℕ = smax-oneR
codeMaxR CType = smax-oneR
codeMaxR (CΠ c cod) = smax-oneR
codeMaxR (CΣ c cod) = smax-oneR
codeMaxR (C≡ c x y) = smax-oneR
codeMaxR (Cμ tyCtor c D x) = smax-oneR
codeMaxR {ℓ = suc ℓ} (CCumul c) = codeMaxR c

codeMaxSuc : ∀ {ℓ1 ℓ2} {c1 : ℂ ℓ1 } {c2 : ℂ ℓ2} → S1 ≤ₛ smax (codeSize c1) (codeSize c2)
codeMaxSuc {c1 = c1} {c2 = c2} = ≤ₛ-sucMono ≤ₛ-Z ≤⨟ smax-strictMono (codeSuc c1) (codeSuc c2)


⁇suc : ∀ {{_ : Æ}} {ℓ} {mi} (x : ⁇CombinedTy ℓ mi) → S1 ≤ₛ ⁇Size x
⁇suc (⁇fromGerm x) = ≤ₛ-sucMono ≤ₛ-Z
⁇suc ⁇⁇ = ≤ₛ-sucMono ≤ₛ-refl -- ≤ₛ-sucMono ≤ₛ-Z
⁇suc ⁇℧ = ≤ₛ-sucMono ≤ₛ-refl -- ≤ₛ-sucMono ≤ₛ-Z
⁇suc ⁇𝟙 = ≤ₛ-sucMono ≤ₛ-refl -- ≤ₛ-sucMono ≤ₛ-Z
⁇suc (⁇ℕ n) = ≤ₛ-sucMono ≤ₛ-Z
⁇suc {suc ℓ} (⁇Type x) = ≤ₛ-sucMono ≤ₛ-Z
⁇suc (⁇Π x) = ≤ₛ-sucMono ≤ₛ-Z
⁇suc (⁇Σ x) = ≤ₛ-sucMono ≤ₛ-Z
⁇suc (⁇≡ (x ⊢ .⁇⁇ ≅ .⁇⁇)) = ≤ₛ-sucMono ≤ₛ-Z
⁇suc (⁇μ tyCtor x) = ≤ₛ-sucMono ≤ₛ-Z
⁇suc {ℓ = suc ℓ} (⁇Cumul c x) = ≤ₛ-sucMono ≤ₛ-Z

