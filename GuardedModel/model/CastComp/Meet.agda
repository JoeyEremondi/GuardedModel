

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

open import ApproxExact
open import InductiveCodes
open import CodeSize
-- open import CodePair
open import WMuEq
open import Ord

open import CastComp.Interface

module CastComp.Meet {{dt : DataTypes}} {{dg : DataGerms}} {{ic : InductiveCodes}} {{dgs : DataGermsSmaller}}
    {ℓ} (cSize : Ord) (vSize : Ord) (scm : SmallerCastMeet ℓ cSize vSize)

  where

open import Code
open import Head
open import Util


open SmallerCastMeet scm



⁇meet : ∀
      {{_ : Æ}}
      {vh1 vh2}
      (x y : ⁇Ty ℓ)
      → (cpf : O1 ≡p cSize)
      → ( cpf : omax (elSize C⁇ x) (elSize C⁇ y)  ≡p vSize )
      → (ceq : codeHead C⁇ ≡p H⁇)
      → (veq1 : valueHead C⁇ ceq x ≡p vh1)
      → (veq2 : valueHead C⁇ ceq y ≡p vh2)
      → ValHeadMatchView vh1 vh2
      → LÆ (⁇Ty ℓ)
⁇meet x y reflp reflp reflp veq1 veq2 (VH℧L pf) = pure ⁇℧
⁇meet x y reflp reflp ceq veq1 veq2 (VH℧R x₁) = pure ⁇℧
⁇meet x y reflp reflp ceq veq1 veq2 (VHNeq⁇ x₁) = pure ⁇℧
⁇meet x y reflp reflp ceq veq1 veq2 (VHIn⁇L x₁ x₂) = pure y
⁇meet x y reflp reflp ceq veq1 veq2 (VHIn⁇R x₁) = pure x
⁇meet (⁇Cumul x) y reflp reflp reflp veq1 veq2 (VHEq⁇ reflp) = {!!}
⁇meet x (⁇Cumul y)  reflp reflp reflp veq1 veq2 (VHEq⁇ reflp) = {!!}
⁇meet x y reflp reflp reflp veq1 veq2 (VHEq⁇ reflp) with (pTrans veq1 (pSym veq2))
... | eq = {!x y !}

meet : ∀ {{æ : Æ}}
      → (c : ℂ ℓ)
      → (x y : El c)
      → ( pfc1 : (codeSize c)  ≡p cSize )
      → ( pfv1 : omax (elSize c x) (elSize c y)  ≡p vSize )
      → LÆ (El c)
meet C⁇ x y pfc pfv = {!!}
meet C℧ x y pfc pfv = pure tt
meet C𝟘 x y pfc pfv = pure tt
meet C𝟙 x y pfc pfv = pure (x and y)
meet (CType {{suc<}}) c1 c2 pfc pfv = pure (oCodeMeet ℓself c1 c2 reflp reflp)
meet (CCumul {{suc<}} c) x y pfc pfv = oMeet ℓself c x y reflp reflp
meet (CΠ dom cod) f g reflp reflp
  = liftFunDep λ x →
    cod (approx x) ∋ f x ⊓ g x
      By hide {arg = ≤o-sucMono (≤o-cocone ⦃ æ = Approx ⦄ _ _ (omax∞-self _) ≤⨟ omax-≤R ≤⨟ omax∞-self _ ≤⨟ omax∞-distR)}
meet (CΣ dom cod) (xfst , xsnd) (yfst , ysnd) reflp reflp = do
  -- Awful stuff to deal with the lifting monad
  x⊓yfst ← withApproxL' λ æ conv → [ æ ] dom ∋ exact {{æ = æ}} (conv xfst) ⊓ exact {{æ = æ}} (conv yfst)
    By hide {arg = ≤o-sucMono (omax∞-self _ ≤⨟ omax-≤L)}
  xsnd-cast ← ⟨ cod (approx x⊓yfst) ⇐ cod (approx xfst) ⟩ xsnd
    By hide {arg = ≤o-sucMono (omax∞-lub
      (≤o-cocone ⦃ æ = Approx ⦄ _ _ (omax∞-self _) ≤⨟ omax∞-self _)
      (≤o-cocone ⦃ æ = Approx ⦄ _ _ (omax∞-self _) ≤⨟ omax∞-self _)
       ≤⨟ omax-≤R)}
  ysnd-cast ← ⟨ cod (approx x⊓yfst) ⇐ cod (approx yfst) ⟩ ysnd
    By hide {arg = ≤o-sucMono (omax∞-lub
      (≤o-cocone ⦃ æ = Approx ⦄ _ _ (omax∞-self _) ≤⨟ omax∞-self _)
      (≤o-cocone ⦃ æ = Approx ⦄ _ _ (omax∞-self _) ≤⨟ omax∞-self _)
       ≤⨟ omax-≤R)}
  x⊓ysnd ← cod (approx x⊓yfst) ∋ xsnd-cast ⊓ ysnd-cast
    By hide {arg = ≤o-sucMono (≤o-cocone ⦃ æ = Approx ⦄ _ _ (omax∞-self _) ≤⨟ omax-≤R ≤⨟ omax∞-self _ ≤⨟ omax∞-distR)}
  pure (x⊓yfst , x⊓ysnd)
meet (C≡ c x y) (w1 ⊢ _ ≅ _) (w2 ⊢ _ ≅ _) reflp reflp = do
  w ←  [ Approx ] c ∋ w1 ⊓ w2
    By hide {arg = ≤o-sucMono (omax∞-self _)}
  pure (w ⊢ x ≅ y)

meet (Cμ tyCtor c D x₁) x y pfc pfv = {!!}
