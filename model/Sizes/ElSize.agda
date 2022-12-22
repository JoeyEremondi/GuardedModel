


{-# OPTIONS --cubical --guarded -v term:50 #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
-- open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat as Nat
import Cubical.Data.Nat.Order as Nat
import Cubical.Induction.WellFounded as Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool
-- open import Cubical.Data.Equality
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import UnkGerm
open import GuardedAlgebra
import GuardedModality as G
open import Cubical.Induction.WellFounded
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import InductiveCodes
open import W
-- open import Cubical.Data.Equality using (ptoc)

open import ApproxExact
open import GTypes
open import Code
open import Head
open import Util

open import Sizes.Size -- ℂ El ℧ C𝟙 refl

open import Sizes.MultiMax
open import Sizes.NatLim

-- open import InductiveCodes
open import Cubical.Foundations.Transport

module Sizes.ElSize {{_ : DataTypes}} {{_ : DataGerms}} {{_ : CodesForInductives }}
    (ℓ : ℕ)
    (smallerCodeSize : {{inst : 0< ℓ}} → ℂ-1 (SmallerCodeAt ℓ ) → Size)
    (smallerElSize : {{æ : Æ }} → {{inst : 0< ℓ}} → (c : ℂ-1 (SmallerCodeAt ℓ)) → El-1 (SmallerCodeAt ℓ) c → Size)
    (elSizeConsumeFuel : ∀ {{æ : Æ}} → (c : ℂ ℓ) → El c → Size)
  where
open import Sizes.CodeSize ℓ smallerCodeSize

GNatSize : GNat → Size
GNatSize (GSuc x) = S↑ (GNatSize x)
GNatSize x = S1


-- germUnkSize' : (x : WUnk {{æ = Approx}} ℓ) → Size
⁇Size' : ∀ {{ æ : Æ}} → ⁇Ty ℓ → Size
GermSize' : ∀ {{ æ : Æ}} {tyCtor : CName} → ⁇GermTy ℓ tyCtor → Size
elSize' : ∀ {{æ : Æ}} (c : ℂ ℓ) → El c → Size
-- ▹elSize' : ∀ {ℓ} (c : ℂ ℓ) → ▹El c → Size
CμSize' : ∀  {{æ : Æ}}  {tyCtor : CName} (D : DCtors ℓ tyCtor) →  ℂμ ℓ tyCtor D → Size
CElSize' : ∀ {{æ : Æ}} {tyCtor : CName} (D : DCtors ℓ tyCtor )  → (E : DCtors ℓ tyCtor)
  →  (cf : ℂFunctor ℓ tyCtor D (ℂμ ℓ tyCtor E))
  → Size


⁇Size' ⁇℧ = S1
⁇Size' ⁇⁇ = S1
⁇Size' ⁇𝟙 = S1
⁇Size' (⁇ℕ n) = S↑ (GNatSize n)
⁇Size' (⁇Type x ) = S↑ (smallerCodeSize x)
⁇Size' (⁇Cumul c x) = S↑ (smallerElSize c x)
⁇Size' (⁇Π f) = S↑ (SLim {ℓ = ℓ} C⁇ λ x → ⁇Size' (f (transport (symPath  ⁇Wrap≡  ) (next (exact {c = C⁇ {ℓ = ℓ}} x)))))
⁇Size' (⁇Σ (x , y)) = S↑ (smax (⁇Size' x) (⁇Size' y))
⁇Size' (⁇≡ (w ⊢ _ ≅ _)) = S↑ (⁇Size' w)
⁇Size' (⁇μ tyCtor x) = S↑ (GermSize' x)

GermSize' DataGerms.⁇℧ = S1
GermSize' DataGerms.⁇⁇ = S1
GermSize' {tyCtor = tyCtor} (DataGerms.Wsup d com germFO germHO germHOUnk)
  = S↑ (smax* (elSizeConsumeFuel (germCommandCode (dataGermIsCode ℓ tyCtor d )) (Iso.fun (germCommandIso (dataGermIsCode ℓ tyCtor d) ) com)
              ∷ FinLim (λ n → GermSize' (germFO n))
              ∷ SLim (germHOCode (dataGermIsCode ℓ tyCtor d) (approx (Iso.fun (germCommandIso (dataGermIsCode ℓ tyCtor d)) com))) (λ r → GermSize' (germHO (Iso.inv (germHOIso (dataGermIsCode ℓ tyCtor d) _) (exact r))))
              ∷ SLim (germHOUnkCode (dataGermIsCode ℓ tyCtor d) (approx (Iso.fun (germCommandIso (dataGermIsCode ℓ tyCtor d)) com))) (λ r → ⁇Size' (germHOUnk (Iso.inv (germHOUnkIso (dataGermIsCode ℓ tyCtor d) _) (exact r)))) ∷ []))

elSize' {{æ = æ}} C⁇ x = ⁇Size' {{æ = æ}} x --germUnkSize' (⁇ToW {{æ = Approx}} (approx {c = C⁇ {ℓ = ℓ}} x))
elSize' C℧ x = S1
elSize' C𝟘 x = S1
elSize' C𝟙 x = S1
elSize' Cℕ x = GNatSize x
elSize' (CType {{inst = inst}}) x = S↑ (smallerCodeSize x)
elSize' {{æ = æ}}  (CΠ dom cod) f = S↑ (SLim dom λ x → elSize' (cod _) (f (exact x))) -- S↑ (SLim dom (λ x → elSize' {{æ = æ}} (substPath (λ x → El (cod x)) (approxExact≡ x) (f (exact x))) ))
elSize' {{æ = æ}} (CΣ dom cod) (x , y) = S↑ (smax (elSize' {{æ = æ}} dom x) (elSize' {{æ = æ}} (cod (approx x)) y)) -- S↑ (smax (elSize' dom (exact x)) (elSize' (cod (approx x)) y))
elSize' (C≡ c x y ) (w ⊢ _ ≅ _) = S↑ (elSize' {{Approx}} c w)
elSize' (Cμ tyCtor cI D i) x = CμSize' D (toℂμ ℓ tyCtor D x)
-- S↑ (smax* (elSize' (coms d) com ∷ (FinLim λ n → elSize' {!!} (res (inl n))) ∷ (SLim (ℂCommand (D d)) λ com → SLim (ℂHOResponse (D d) com) λ x → elSize' (Cμ coms ress) (res (inr (exact _ x)))) ∷ [])) -- S↑ (CμSize' D ( Iso.inv CμWiso (approx {ℓ = ℓ} {c = Cμ tyCtor cI D i} x) ))
elSize' (CCumul {{inst = inst}} c) x = smallerElSize _ x --elSize' c x

CμSize' D  (ℂinit x) = S↑ (CElSize' D D x) -- S↑ (CElSize' (D (ℂFunctor.d x)) D x)
CμSize' D μ⁇ = S1
CμSize' D μ℧ = S1

CElSize' D E (ℂEl d com rFO rHO) = S↑ (smax* (elSize' _ com ∷ (FinLim λ n → CμSize' E (rFO n)) ∷ (SLim (ℂHOResponse (D d) (approx com)) λ r → CμSize' E (rHO (exact r))) ∷ []))

