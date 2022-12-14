

{-# OPTIONS --cubical --guarded  #-}



-- open import Guarded
open import Cubical.Data.Maybe as Maybe
open import Level
open import Cubical.Relation.Nullary

open import DecPEq 
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (⊥ to 𝟘)
-- open import Cubical.Data.Prod
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Inductives
open import GuardedAlgebra
open import Cubical.Induction.WellFounded
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Sum as Sum
open import GuardedModality using (later-ext)

open import ApproxExact
open import Code

--TODO: don't make ℓ module param
module WMuEq {{_ : DataTypes}} {{_ : DataGerms}} where

open import WMuConversion public


-- We only ever attach a size to the approximate part of a computation
-- and we only need this conversion for making a size
private
  instance
    approxÆ : Æ
    approxÆ = Approx

  -- TODO: report Agda issue about why this checks slow without the helper fn
fromToCEl :
  ∀ {ℓ sig} {cI cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI cB sig) (E : DCtors tyCtor cI) {ix : ApproxEl cI} {b : ApproxEl cB}
  → (com : CommandD D ix b)
  → (k : (r : ResponseD D b com ) →
                  WArg E (inextD D b com r))
  → (φ₂ : □ {X = WArg E} (interpDesc D b)
      (λ (i , x) →
          fromCμ (toCμ E x) ≡ x)
      (ix , FC com k))
  → PathP (λ 𝕚 → let com = fromToCElCommand D E com k  𝕚 in (r : ResponseD D b com) → WArg E (inextD D b com r))
  (fromCEl D E (toCEl D E com k λ r → toCμ E (k r))) k
fromToCEl (CEnd i) E com k  φ = funExt (λ ())
fromToCEl (CArg c D _ reflp) E (a , com) k  φ  = fromToCEl D E com k φ
fromToCEl (CRec j D) E com k  φ 𝕚 (Rec tt) = φ (Rec tt) 𝕚
fromToCEl (CRec j D) E com k  φ 𝕚 (Rest r) = fromToCEl D E com (λ r → k (Rest r)) (λ r → φ (Rest r)) 𝕚 r
fromToCEl (CodeModule.CHRec c j D _ reflp) E com k φ = helper
  where
    helper : PathP
                (λ 𝕚 →
                  (r
                    : ResponseD (CHRec c j D (CΣ _ c) reflp) _
                      (fromToCElCommand (CHRec c j D (CΣ _ c) reflp) E com k 𝕚)) →
                  WArg E
                  (inextD (CHRec c j D (CΣ _ c) reflp) _
                    (fromToCElCommand (CHRec c j D (CΣ _ c) reflp) E com k 𝕚) r))
                (fromCEl (CHRec c j D (CΣ _ c) reflp) E
                (toCEl (CHRec c j D (CΣ _ c) reflp) E com k (λ r → toCμ E (k r))))
                k
    helper 𝕚 (Rec x) = φ (Rec x) 𝕚
    helper 𝕚 (Rest x) = fromToCEl D E com (λ r → k (Rest r)) (λ r → φ (Rest r)) 𝕚 x


fromToCμ :  ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} (D : DCtors tyCtor cI) {ix : ApproxEl cI}
  → (x : WArg D ix)
  → fromCμ (toCμ D x) ≡ x
fromToCμ {cI = cI} D = wInd
  (λ(ix , x) → fromCμ (toCμ D x) ≡ x) helper refl refl
  where
    helper : ∀ {i : ApproxEl cI} (cs : ⟦ Arg (λ d → interpDesc (D d) tt)⟧F (WArg D) i)  →  (φ : _) → fromCμ (toCμ D (Wsup cs)) ≡ Wsup cs
    helper {i} (FC (d , com) k) φ 𝕚 =
      Wsup (FC
        (d , fromToCElCommand (D d) D com k 𝕚)
        (fromToCEl (D d) D com k φ 𝕚) )


toFromCμ : ∀ {ℓ} {cI : ℂ ℓ} {tyCtor : CName} {D : DCtors tyCtor cI} {i : ApproxEl cI}
  → (x : ℂμ tyCtor D i)
  → toCμ D (fromCμ x) ≡ x
toFromCEl : ∀ {ℓ sig} {cI cB : ℂ ℓ} {tyCtor : CName} (D : ℂDesc cI cB sig) (E : DCtors tyCtor cI) {i : ApproxEl cI} {b : ApproxEl cB}
  → (x : ℂDescEl  D (ℂμ tyCtor E) i b)
  → toCEl D E (fromCElCommand D x) (fromCEl D E x) (λ r → toCμ E (fromCEl D E x r)) ≡ x

toFromCμ (Cinit d x) = cong (Cinit d) (toFromCEl _ _ x)
toFromCμ Cμ⁇ = refl
toFromCμ Cμ℧ = refl

toFromCEl .(CEnd j) E (ElEnd j x) = refl
toFromCEl (CArg c D _ reflp) E (ElArg a x) = cong (ElArg a) (toFromCEl D E x)
toFromCEl (CRec j D) E (ElRec x x₁) = cong₂ ElRec (toFromCμ x) (toFromCEl D E x₁)
toFromCEl (CHRec c j D _ reflp) E (ElHRec x x₁) = cong₂ ElHRec (funExt (λ a → toFromCμ (x a))) (toFromCEl D E x₁)
-- toFromCEl (CHGuard c D1 D2) E (ElHGuard x x₁) = cong₂ ElHGuard (funExt λ a → toFromCEl D1 E (x a)) (toFromCEl D2 E x₁)




CμWiso :
  ∀ {ℓ} {cI  : ℂ ℓ}  {tyCtor : CName} {D : DCtors tyCtor cI} {i : ApproxEl cI}
  → Iso (ℂμ tyCtor D i) (WArg D i)
CμWiso = (iso fromCμ (toCμ _) (fromToCμ _) toFromCμ)
