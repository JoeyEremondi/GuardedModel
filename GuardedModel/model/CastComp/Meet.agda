

-- Bound on the size of the meet on codes, assuming we have meet, cast, etc. for smaller types


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
open import Cubical.Foundations.Isomorphism

open import ApproxExact
open import InductiveCodes
open import CodeSize
-- open import CodePair
open import WMuEq
open import SizeOrd
open import Assumption

open import CastComp.Interface

module CastComp.Meet {{dt : DataTypes}} {{dg : DataGerms}} {{ic : InductiveCodes}}
    (⁇Allowed : ⁇Flag){ℓ} (cSize : Size) (vSize : Size) (scm : SmallerCastMeet ⁇Allowed ℓ cSize vSize)

  where

open import Code
open import Head
open import Util
open import WellFounded


open SmallerCastMeet scm







⁇meet : ∀
      {{æ : Æ}}
      (x y : ⁇Ty ℓ)
      → (cpf : if¬Pos ⁇Allowed (S1 ≡p cSize) (SZ ≡p cSize))
      → ( vpf : smax (elSize C⁇ x) (elSize C⁇ y)  ≤ₛ vSize )
      → LÆ (⁇Ty ℓ)
⁇meet' : ∀
      {{æ : Æ}}
      {vh1 vh2}
      (x y : ⁇Ty ℓ)
      → (cpf : if¬Pos ⁇Allowed (S1 ≡p cSize) (SZ ≡p cSize))
      → ( vpf : smax (elSize C⁇ x) (elSize C⁇ y)  ≤ₛ vSize )
      → (veq1 : unkHead x ≡p vh1)
      → (veq2 : unkHead y ≡p vh2)
      → HeadMatchView vh1 vh2
      → LÆ (⁇Ty ℓ)

⁇meet x y cpf vpf = ⁇meet' x y cpf vpf reflp reflp (headMatchView (unkHead x) (unkHead y))

⁇meet' x y cpf lt eqx eqy (H℧L x₁) = pure ⁇℧
⁇meet' x y cpf lt eqx eqy (H℧R x₁) = pure ⁇℧
⁇meet' x y cpf lt eqx eqy (HNeq x₁) = pure ⁇℧
⁇meet' x y cpf lt eqx eqy (H⁇L x₁ x₂) = pure y
⁇meet' x y cpf lt eqx eqy (H⁇R x₁) = pure x
⁇meet' x y cpf lt eqx eqy (HEq reflp) with pTrans eqx (pSym eqy)
⁇meet' CodeModule.⁇𝟙 CodeModule.⁇𝟙 cpf lt eqx eqy (HEq reflp) | eq = pure ⁇𝟙
⁇meet' (CodeModule.⁇Type {{suc<}} c1) (CodeModule.⁇Type c2) cpf lt eqx eqy (HEq reflp) | eq
  = pure (⁇Type {{inst = suc<}} (oCodeMeet (self-1 {{suc<}}) reflp c1 c2 reflp reflp))
⁇meet' (CodeModule.⁇Cumul {{suc<}} c1 x1) (CodeModule.⁇Cumul c2 x2) cpf lt eqx eqy (HEq reflp) | eq
  -- Cast to a common code type, then meet
  = do
  let c1⊓c2 = oCodeMeet (self-1 {{suc<}}) reflp c1 c2 reflp reflp
  (x1' , lt1) ← oCast (self-1 {{suc<}}) c1 c1⊓c2 reflp x1 reflp
  (x2' , lt2) ← oCast (self-1 {{suc<}}) c2 c1⊓c2 reflp x2 reflp
  x1⊓x2 ← oMeet (self-1 {{suc<}}) c1⊓c2 x1' x2' reflp reflp
  pure (⁇Cumul {{inst = suc<}} c1⊓c2 x1⊓x2)
⁇meet' {{æ = Approx}} (CodeModule.⁇Π f1) (CodeModule.⁇Π f2) cpf lt eqx eqy (HEq reflp) | eq
  = pure ⦃ Approx ⦄ (⁇Π ⦃ _ ⦄ ⦃ _ ⦄ ⦃ Approx ⦄ (λ _ → fromL (⁇meet ⦃ Approx ⦄ (f1 U⁇) (f2 U⁇) cpf
    (smax-mono
      (≤suc (≤ₛ-cocone {{æ = Approx}} (f1 U⁇)))
      (≤suc (≤ₛ-cocone {{æ = Approx}} (f1 U⁇)))
    ≤⨟ lt))))
⁇meet' {{æ = Exact}} (CodeModule.⁇Π f1) (CodeModule.⁇Π f2) cpf lt eqx eqy (HEq reflp) | eq
  = do
    fRet ← liftFun {{Exact}} λ x → do
      gSelf ← Later {{Exact}} λ tic → pure ⦃ Exact ⦄ (▹self {⁇Allowed = ⁇Allowed} {ℓ' = ℓ} tic)
      oMeet gSelf {{æ = Exact}} C⁇ (f1 x) (f2 x) cpf reflp
    pure {{Exact}} (⁇Π ⦃ _ ⦄ ⦃ _ ⦄ ⦃ Exact ⦄ fRet)
⁇meet' (CodeModule.⁇Σ (fst1 , snd1)) (CodeModule.⁇Σ (fst2 , snd2)) cpf lt eqx eqy (HEq reflp) | eq = {!!}
⁇meet' (CodeModule.⁇≡ x) (CodeModule.⁇≡ x₁) cpf lt eqx eqy (HEq reflp) | eq = {!!}
⁇meet' (CodeModule.⁇μ tyCtor x) (CodeModule.⁇μ tyCtor₁ y) cpf lt eqx eqy (HEq reflp) | reflp = do
  x⊓y ← germIndMeet {posNoCode = λ {reflp → cpf}} {cpf} x y (<≤ (smax-strictMono ≤ₛ-refl ≤ₛ-refl) lt)
  pure (⁇μ tyCtor x⊓y)



-- meet : ∀ {{æ : Æ}}
--       → (c : ℂ ℓ)
--       → (x y : El c)
--       → ( pfc1 : (codeSize c)  ≡p cSize )
--       → ( pfv1 : smax (elSize c x) (elSize c y)  ≡p vSize )
--       → LÆ (El c)
-- meet C⁇ x y pfc pfv = ⁇meet x y pfc (pSubst (λ x → _ ≤ₛ x) pfv ≤ₛ-refl)
-- meet C℧ x y pfc pfv = pure tt
-- meet C𝟘 x y pfc pfv = pure tt
-- meet C𝟙 x y pfc pfv = pure (x and y)
-- meet (CType {{suc<}}) c1 c2 pfc pfv = pure (oCodeMeet (self-1 {{suc<}}) c1 c2 reflp reflp)
-- meet (CCumul {{suc<}} c) x y pfc pfv = oMeet (self-1 {{suc<}}) c x y reflp reflp
-- meet (CΠ dom cod) f g reflp reflp
--   = liftFunDep λ x →
--     cod (approx x) ∋ f x ⊓ g x
--       cBy hide {arg = ≤ₛ-sucMono (≤ₛ-cocone ⦃ æ = Approx ⦄ _  ≤⨟ smax-≤R  )}
--       vBy ?
-- meet (CΣ dom cod) (xfst , xsnd) (yfst , ysnd) reflp reflp = do
--   -- Awful stuff to deal with the lifting monad
--   x⊓yfst ← withApproxL' λ æ conv →
--     [ æ ] dom ∋ exact {{æ = æ}} (conv xfst) ⊓ exact {{æ = æ}} (conv yfst)
--       cBy hide {arg = ≤ₛ-sucMono  smax-≤L}
--       vBy ?
--   xsnd-cast ← ⟨ cod (approx x⊓yfst) ⇐ cod (approx xfst) ⟩ xsnd
--     cBy hide {arg = ≤ₛ-sucMono (smax-lub
--       (≤ₛ-cocone ⦃ æ = Approx ⦄ _)
--       (≤ₛ-cocone ⦃ æ = Approx ⦄  _)
--        ≤⨟ smax-≤R)}
--     vBy ?
--   ysnd-cast ← ⟨ cod (approx x⊓yfst) ⇐ cod (approx yfst) ⟩ ysnd
--     cBy hide {arg = ≤ₛ-sucMono (smax-lub
--       (≤ₛ-cocone ⦃ æ = Approx ⦄  _)
--       (≤ₛ-cocone ⦃ æ = Approx ⦄  _)
--        ≤⨟ smax-≤R)}
--     vBy ?
--   x⊓ysnd ←
--     cod (approx x⊓yfst) ∋ xsnd-cast ⊓ ysnd-cast
--         cBy hide {arg = ≤ₛ-sucMono (≤ₛ-cocone ⦃ æ = Approx ⦄ _  ≤⨟ smax-≤R )}
--         vBy ?
--   pure (x⊓yfst , x⊓ysnd)
-- meet (C≡ c x y) (w1 ⊢ _ ≅ _) (w2 ⊢ _ ≅ _) reflp reflp = do
--   w ←  [ Approx ] c ∋ w1 ⊓ w2
--     cBy hide {arg = ≤ₛ-refl}
--     vBy ?
--   pure (w ⊢ x ≅ y)

-- meet (Cμ tyCtor c D x₁) x y pfc pfv = {!!}
