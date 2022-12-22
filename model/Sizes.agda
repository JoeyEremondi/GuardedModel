{-# OPTIONS --cubical --guarded --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import UnkGerm
open import InductiveCodes
open import Cubical.Data.Nat

module Sizes {{_ : DataTypes}} {{_ : DataGerms}} {{_ : CodesForInductives }} where

open import Sizes.Size public
open import Sizes.MultiMax public
open import Sizes.CodeSize public
open import Sizes.ElSize public
open import Sizes.NatLim public
open import Sizes.WellFounded public

open import Code
open import ApproxExact

smallerCodeSize : ∀ {ℓ} {{inst : 0< ℓ}} → ℂ-1 (SmallerCodeAt ℓ) → Size
codeSizeFuel : ∀ {ℓ} → ℕ → (c : ℂ ℓ) → Size
codeSize : ∀ {ℓ} → ℂ ℓ → Size

-- Calculates the code size for codes from lower (universe) levels
smallerCodeSize {suc ℓ}  = codeSize
-- We have a function, codeSizeFuel, that with fuel suc n, sets the size of ⁇ to be
-- the greater than the limit of all code sizes calculated with fuel n
codeSizeFuel zero = λ _ → SZ
codeSizeFuel {ℓ = ℓ} (suc n) = codeSize' ℓ smallerCodeSize (codeSizeFuel n)
-- Then, the actual code size is the limit over all fuel values
codeSize {ℓ = ℓ} c = codeSize' ℓ smallerCodeSize (λ c → ℕLim λ n → codeSizeFuel n c) c



elSizeFuel : ∀ {{æ : Æ}} {ℓ} → ℕ → (c : ℂ ℓ) → El c → Size
smallerElSize :  ∀ {{æ : Æ}} {ℓ} {{inst : 0< ℓ}} → (c : ℂ-1 (SmallerCodeAt ℓ)) → El-1 (SmallerCodeAt ℓ) c → Size
elSize : ∀ {{æ : Æ}} {ℓ} → (c : ℂ ℓ) → El c → Size

smallerElSize {ℓ = suc ℓ} = elSize

elSizeFuel {ℓ = ℓ} zero = elSize' ℓ smallerCodeSize smallerElSize (λ _ _ → SZ)
elSizeFuel {ℓ = ℓ} (suc n) = elSize' ℓ smallerCodeSize smallerElSize (elSizeFuel n)

-- We take the limit of the fueled sizes to get the full size
elSize {ℓ} c x = ℕLim (λ n → elSize' ℓ smallerCodeSize smallerElSize (elSizeFuel n) c x)

⁇Size : ∀ {{æ : Æ}} {ℓ} → ⁇Ty ℓ → Size
⁇SizeFuel : ∀ {{æ : Æ}} {ℓ} → ℕ → ⁇Ty ℓ → Size

⁇SizeFuel {ℓ = ℓ} n = ⁇Size' ℓ smallerCodeSize smallerElSize (elSizeFuel n)
⁇Size x = ℕLim λ n → ⁇SizeFuel n x

GermSize : ∀ {{æ : Æ}} {ℓ tyCtor} → ⁇GermTy ℓ tyCtor → Size
GermSizeFuel : ∀ {{æ : Æ}} {ℓ tyCtor} → ℕ → ⁇GermTy ℓ tyCtor → Size
GermSizeFuel {ℓ = ℓ} n = GermSize' ℓ smallerCodeSize smallerElSize (elSizeFuel n)
GermSize x = ℕLim λ n → GermSizeFuel n x

-- codeSuc : ∀ {ℓ} (c : ℂ ℓ) → SZ <ₛ codeSize c
-- codeSuc C⁇ = ℕsucMono ≤ₛ-Z
-- codeSuc C℧ =  ℕsucMono  ≤ₛ-Z
-- codeSuc C𝟘 = ℕsucMono  ≤ₛ-Z
-- codeSuc C𝟙 = ℕsucMono ≤ₛ-Z
-- codeSuc Cℕ = ℕsucMono ≤ₛ-Z
-- codeSuc CType = ℕsucMono ≤ₛ-Z
-- codeSuc (CΠ c cod) = ℕsucMono ≤ₛ-Z
-- codeSuc (CΣ c cod) = ℕsucMono ≤ₛ-Z
-- codeSuc (C≡ c x y) = ℕsucMono ≤ₛ-Z
-- codeSuc (Cμ tyCtor c D x) = ℕsucMono ≤ₛ-Z
-- codeSuc {ℓ = suc ℓ} (CCumul c) = ℕsucMono ≤ₛ-Z

-- codeMaxL : ∀ {ℓ} (c : ℂ ℓ) → smax S1 (codeSize c) ≤ₛ codeSize c
-- codeMaxL C⁇ = ℕmaxL ≤⨟ ℕLim-ext smax-oneL -- ℕsucMono smax-oneL
-- codeMaxL C℧ = ℕmaxL ≤⨟ ℕLim-ext smax-oneL
-- codeMaxL C𝟘 = ℕmaxL ≤⨟ ℕLim-ext smax-oneL
-- codeMaxL C𝟙 = ℕmaxL ≤⨟ ℕLim-ext smax-oneL
-- codeMaxL Cℕ = ℕmaxL ≤⨟ ℕLim-ext smax-oneL
-- codeMaxL CType = ℕmaxL ≤⨟ ℕLim-ext smax-oneL
-- codeMaxL (CΠ c cod) = ℕmaxL ≤⨟ ℕLim-ext smax-oneL
-- codeMaxL (CΣ c cod) = ℕmaxL ≤⨟ ℕLim-ext smax-oneL
-- codeMaxL (C≡ c x y) = ℕmaxL ≤⨟ ℕLim-ext smax-oneL
-- codeMaxL (Cμ tyCtor c D x) = ℕmaxL ≤⨟ ℕLim-ext smax-oneL
-- codeMaxL {ℓ = suc ℓ} (CCumul c) = ℕmaxL ≤⨟ ℕLim-ext smax-oneL


-- codeMaxR : ∀ {ℓ} (c : ℂ ℓ) → smax (codeSize c) S1 ≤ₛ codeSize c
-- codeMaxR C⁇ = ℕmaxR ≤⨟ ℕLim-ext smax-oneR
-- codeMaxR C℧ = ℕmaxR ≤⨟ ℕLim-ext smax-oneR
-- codeMaxR C𝟘 = ℕmaxR ≤⨟ ℕLim-ext smax-oneR
-- codeMaxR C𝟙 = ℕmaxR ≤⨟ ℕLim-ext smax-oneR
-- codeMaxR Cℕ = ℕmaxR ≤⨟ ℕLim-ext smax-oneR
-- codeMaxR CType = ℕmaxR ≤⨟ ℕLim-ext smax-oneR
-- codeMaxR (CΠ c cod) = ℕmaxR ≤⨟ ℕLim-ext smax-oneR
-- codeMaxR (CΣ c cod) = ℕmaxR ≤⨟ ℕLim-ext smax-oneR
-- codeMaxR (C≡ c x y) = ℕmaxR ≤⨟ ℕLim-ext smax-oneR
-- codeMaxR (Cμ tyCtor c D x) = ℕmaxR ≤⨟ ℕLim-ext smax-oneR
-- codeMaxR {ℓ = suc ℓ} (CCumul c) = ℕmaxR ≤⨟ ℕLim-ext smax-oneR

-- codeMaxSuc : ∀ {ℓ1 ℓ2} {c1 : ℂ ℓ1 } {c2 : ℂ ℓ2} → S1 ≤ₛ smax (codeSize c1) (codeSize c2)
-- codeMaxSuc {c1 = c1} {c2 = c2} = ≤ₛ-sucMono ≤ₛ-Z ≤⨟ smax-strictMono (codeSuc c1) (codeSuc c2)


-- ⁇suc : ∀ {{_ : Æ}} {ℓ} (x : ⁇Ty ℓ) → S1 ≤ₛ ⁇Size x
-- ⁇suc ⁇⁇ = ℕsucMono ≤ₛ-refl -- ≤ₛ-sucMono ≤ₛ-Z
-- ⁇suc ⁇℧ = ℕsucMono ≤ₛ-refl -- ≤ₛ-sucMono ≤ₛ-Z
-- ⁇suc ⁇𝟙 = ℕsucMono ≤ₛ-refl -- ≤ₛ-sucMono ≤ₛ-Z
-- ⁇suc (⁇ℕ n) = ℕsucMono ≤ₛ-Z
-- ⁇suc {suc ℓ} (⁇Type x) = ℕsucMono ≤ₛ-Z
-- ⁇suc (⁇Π x) = ℕsucMono ≤ₛ-Z
-- ⁇suc (⁇Σ x) = ℕsucMono ≤ₛ-Z
-- ⁇suc (⁇≡ (x ⊢ .⁇⁇ ≅ .⁇⁇)) = ℕsucMono ≤ₛ-Z
-- ⁇suc (⁇μ tyCtor x) = ℕsucMono ≤ₛ-Z
-- ⁇suc {ℓ = suc ℓ} (⁇Cumul c x) = ℕsucMono ≤ₛ-Z

-- open import Cubical.Data.Maybe
