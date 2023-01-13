

-- Bound on the size of the meet on codes, assuming we have meet, cast, etc. for smaller types


open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Constructors
open import UnkGerm
open import GuardedAlgebra
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import ApproxExact
open import InductiveCodes
open import Sizes
-- open import CodePair

open import CastComp.Interface

module CastComp.Meet {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ} (cSize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed cSize )

  where

open import Code
open import Head
open import Util
open import GTypes

open import W

open SmallerCastMeet scm
open import WMuConversion
open import CastComp.DescElMeet ⁇Allowed cSize  scm

pureTag : ∀ {{æ : Æ}} {h} → ⁇CombinedTy ℓ  (just h) → LÆ (⁇Ty ℓ)
pureTag x = pure (⁇Tag x)

⁇meet : ∀ {{æ : Æ}} {mi}
  → (x y : ⁇CombinedTy ℓ mi)
  → LÆ (⁇Ty ℓ)
-- inline bind for the termination checker
⁇bindMeet : ∀ {{æ : Æ}} {mi}
  → (x y : LÆ (⁇CombinedTy ℓ mi))
  → LÆ (⁇Ty ℓ)
-- Comparing elements of the same germ type
⁇meet ⁇⁇ y  = pure y
⁇meet x ⁇⁇  = pure x
⁇meet ⁇℧ y  = pure ⁇℧
⁇meet x ⁇℧  = pure ⁇℧
⁇meet ⁇𝟙 ⁇𝟙  = pure (⁇Tag ⁇𝟙)
⁇meet (⁇ℕ x) (⁇ℕ x₁)  = pureTag (⁇ℕ (natMeet x x₁))
⁇meet (⁇Type {{inst = suc<}} c1) (⁇Type {{inst = inst}} c2)
  = pureTag (⁇Type {{inst = inst}} (oCodeMeet (self-1 {{inst}}) c1 c2 reflp ))
-- Since they might not be at the same type, we find the meet of the codes
-- in the smaller unverse, cast to that type, then find the meet at that type
⁇meet (⁇Cumul {{inst = suc<}} c1 x1) (⁇Cumul {{inst = inst}} c2 x2)  =
  do
    let c1⊓c2 = oCodeMeet (self-1 {{inst}}) c1 c2 reflp
    x1-12 ← oCast (self-1 {{inst}}) c1 c1⊓c2 x1 reflp
    x2-12 ← oCast (self-1 {{inst}}) c2 c1⊓c2 x2 reflp
    x1⊓x2 ← oMeet (self-1 {{inst}}) c1⊓c2 x1-12 x2-12 reflp
    pureTag (⁇Cumul {{inst = inst}} c1⊓c2 x1⊓x2)

⁇meet {{æ = æ}} (⁇Π apr1 f1) (⁇Π apr2 f2)  =
  do
    let fRet =  λ pf x → ⁇bindMeet (f1 pf x) (f2 pf x)
    let approxRet = fromL (⁇meet {{æ = Approx}} (apr1 tt) (apr2 tt))
    pureTag (⁇Π (λ _ → approxRet) fRet)
⁇meet (⁇Σ (x1 , y1)) (⁇Σ (x2 , y2))  = do
  x12 ← ⁇meet x1 x2
  y12 ← ⁇meet y1 y2
  pureTag (⁇Σ (x12 , y12))
⁇meet (⁇≡ (w1 ⊢ _ ≅ _)) (⁇≡ (w2 ⊢ _ ≅ _))  =
  do
    w12 ← ⁇meet w1 w2
    pureTag (⁇≡ (w12 ⊢ _ ≅ _))
⁇meet {{æ = æ}} (⁇μ d1 resp1 exact1) (⁇μ d2 resp2 exact2) with decFin d1 d2
... | no _ = pure ⁇℧
... | yes reflp =
  do
    let
      respRet : (r : GermResponse (germCtor ℓ _ d1)) →  _
      respRet r = fromL (⁇meet {{æ = Approx}} (resp1 r) (resp2 r))
      exactRet : (IsExact æ) → (r : GermResponse (germCtor ℓ _ d1)) →  _
      exactRet pf r = ⁇bindMeet (exact1 pf r) (exact2 pf r)
    pureTag (⁇μ d1 respRet exactRet)
-- For two elements of ⁇Ty ℓ, we see if they have the same head
-- If they do, we take the meet at the germ type
-- otherwise, error
⁇meet (⁇Tag{h = h1} x) (⁇Tag {h = h2} y)  with headDecEq h1 h2
... | yes reflp = ⁇meet x y
... | no _ = pure ⁇℧

⁇bindMeet (Now x) (Now y) = ⁇meet x y
⁇bindMeet (Later x) y = Later λ tic → ⁇bindMeet (x tic) y
⁇bindMeet x (Later y) = Later λ tic → ⁇bindMeet x (y tic)



meet : ∀ {{æ : Æ}}
      → (c : ℂ ℓ)
      → (x y : El c)
      → ( pfc1 : (codeSize c)  ≡p cSize )
      → LÆ (El c)
meet C⁇ x y reflp = ⁇meet x y
meet C℧ x y pfc = pure ℧𝟘
meet C𝟘 x y pfc = pure ℧𝟘
-- If either is error, then result is error
meet C𝟙 x y pfc = pure (𝟙meet x y)
-- For Nats, if either is ⁇ then return the other
-- If both are zero, then zero, and if both are suc, compose the smaller numbers
-- Otherwise, error
meet Cℕ x y pfc = pure (natMeet x y)
meet (CType {{suc<}}) c1 c2 pfc = pure (oCodeMeet self-1 c1 c2 reflp)
meet (CCumul {{suc<}} c) x y pfc = oMeet self-1 c x y reflp
meet {{æ = Approx}} (CΠ dom cod) f g reflp = do
  let
    retFun = λ x → do
      let fx = f x
      pure {{æ = Approx}} {!!}
  pure {{æ = Approx}} {!!}
  --   cod (approx x) ∋ f x ⊓ g x
  --     By hide {arg = ≤ₛ-sucMono (≤ₛ-cocone _  ≤⨟ smax-≤R  )}
meet {{æ = Exact}} (CΠ dom cod) f g reflp = {!!}
meet (CΣ dom cod) (xfst , xsnd) (yfst , ysnd) reflp =
  do
  -- Awful stuff to deal with the lifting monad
    x⊓yfst ←
      dom ∋ xfst ⊓ yfst
        By Decreasing
          ≤ₛ-sucMono  smax-≤L
    xsnd-cast ← ⟨ cod (approx x⊓yfst) ⇐ cod (approx xfst) ⟩ xsnd
      By hide {arg = ≤ₛ-sucMono (smax-lub
        (≤ₛ-cocone _)
        (≤ₛ-cocone  _)
        ≤⨟ smax-≤R)}
    ysnd-cast ← ⟨ cod (approx x⊓yfst) ⇐ cod (approx yfst) ⟩ ysnd
      By hide {arg = ≤ₛ-sucMono (smax-lub
        (≤ₛ-cocone   _)
        (≤ₛ-cocone   _)
        ≤⨟ smax-≤R)}
    x⊓ysnd ←
      cod (approx x⊓yfst) ∋ xsnd-cast ⊓ ysnd-cast
          By hide {arg = ≤ₛ-sucMono (≤ₛ-cocone  _  ≤⨟ smax-≤R )}
    pure (x⊓yfst , x⊓ysnd)
meet (C≡ c x y) (w1 ⊢ _ ≅ _) (w2 ⊢ _ ≅ _) reflp = do
  let
    w = c ∋ w1 ⊓ w2
      approxBy hide {arg = ≤ₛ-refl}
  pure (w ⊢ x ≅ y)

meet (Cμ tyCtor c D x₁) x y pfc = {!x y !}
