

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
open import Cubical.Data.Equality
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
    (⁇Allowed : Bool) {ℓ} (cSize : Size) (vSize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed cSize vSize)

  where

open import Code
open import Head
open import Util
open import GTypes

open import W

open SmallerCastMeet scm
open import WMuConversion



⁇meet : ∀ {{æ : Æ}} {mi}
  → (x y : ⁇CombinedTy ℓ mi)
  → LÆ (⁇CombinedTy ℓ mi)
-- Comparing elements of the same germ type
⁇meet ⁇⁇ y  = pure y
⁇meet x ⁇⁇  = pure x
⁇meet ⁇℧ y  = pure ⁇℧
⁇meet x ⁇℧  = pure ⁇℧
⁇meet ⁇𝟙 ⁇𝟙  = pure ⁇𝟙
⁇meet (⁇ℕ x) (⁇ℕ x₁)  = pure (⁇ℕ (natMeet x x₁))
⁇meet (⁇Type {{inst = suc<}} c1) (⁇Type {{inst = inst}} c2)
  = pure (⁇Type {{inst = inst}} (oCodeMeet (self-1 {{inst}}) c1 c2 reflp reflp))
-- Since they might not be at the same type, we find the meet of the codes
-- in the smaller unverse, cast to that type, then find the meet at that type
⁇meet (⁇Cumul {{inst = suc<}} c1 x1) (⁇Cumul {{inst = inst}} c2 x2)  =
  do
    let c1⊓c2 = oCodeMeet (self-1 {{inst}}) c1 c2 reflp reflp
    x1-12 ← oCast (self-1 {{inst}}) c1 c1⊓c2 x1 reflp reflp
    x2-12 ← oCast (self-1 {{inst}}) c2 c1⊓c2 x2 reflp reflp
    x1⊓x2 ← oMeet (self-1 {{inst}}) c1⊓c2 x1-12 x2-12 reflp reflp
    pure (⁇Cumul {{inst = inst}} c1⊓c2 x1⊓x2)

⁇meet (⁇Π f1) (⁇Π f2)  =
  do
    fRet ← liftFun λ x → ⁇meet (f1 x) (f2 x)
    pure (⁇Π fRet)
⁇meet (⁇Σ (x1 , y1)) (⁇Σ (x2 , y2))  = do
  x12 ← ⁇meet x1 x2
  y12 ← ⁇meet y1 y2
  pure (⁇Σ (x12 , y12))
⁇meet (⁇≡ (w1 ⊢ _ ≅ _)) (⁇≡ (w2 ⊢ _ ≅ _))  =
  do
    w12 ← ⁇meet w1 w2
    pure (⁇≡ (w12 ⊢ _ ≅ _))
⁇meet (⁇μ d1 resp1) (⁇μ d2 resp2) with decFin d1 d2
... | no _ = pure ⁇℧
... | yes reflp =
  do
    let
      respRet : (r : GermResponse (germCtor ℓ _ d1)) → LÆ _
      respRet r = ⁇meet (resp1 r) (resp2 r)
    Lret ← liftFunDep respRet
    pure (⁇μ d1 Lret)
-- For two elements of ⁇Ty ℓ, we see if they have the same head
-- If they do, we take the meet at the germ type
-- otherwise, error
⁇meet (⁇fromGerm {h = h1} x) (⁇fromGerm {h = h2} y)  with headDecEq h1 h2
... | yes reflp =
  do
    retMeet ← ⁇meet x y
    pure (⁇fromGerm retMeet)
... | no _ = pure ⁇℧



descElMeet : ∀ {{æ : Æ}} {cB cBTarget : ℂ ℓ} {tyCtor skel oTop}
      → (D : ℂDesc  cB skel)
      → (E : DCtors ℓ tyCtor)
      → (b : ApproxEl cB)
      → (x y : ℂDescEl D (ℂμ tyCtor E) b )
      → (lto : oTop <ₛ cSize )
      → (ltB : (codeSize cBTarget ≤ₛ (codeSize cB) ))
      → (lt : descSize D ≤ₛ  oTop)
      → LÆ (ℂDescEl D (ℂμ tyCtor E) b)
descElMeet CEnd E b ElEnd ElEnd lto ltB lt = pure ElEnd
descElMeet (CArg c x D .(CΣ _ c) .reflp) E b (ElArg a1 rest1) (ElArg a2 rest2) lto ltB lt = do
  pure (ElArg {!!} {!!})
descElMeet (CRec c x D .(CΣ _ c) .reflp) E b (ElRec f1 rest1) (ElRec f2 rest2) lto ltB lt = do
  pure (ElRec ? ?)


meet : ∀ {{æ : Æ}}
      → (c : ℂ ℓ)
      → (x y : El c)
      → ( pfc1 : (codeSize c)  ≡p cSize )
      → ( pfv1 : smax (elSize c x) (elSize c y)  ≡p vSize )
      → LÆ (El c)
meet C⁇ x y reflp pfv = ⁇meet x y
meet C℧ x y pfc pfv = pure ℧𝟘
meet C𝟘 x y pfc pfv = pure ℧𝟘
-- If either is error, then result is error
meet C𝟙 x y pfc pfv = pure (𝟙meet x y)
-- For Nats, if either is ⁇ then return the other
-- If both are zero, then zero, and if both are suc, compose the smaller numbers
-- Otherwise, error
meet Cℕ x y pfc pfv = pure (natMeet x y)
meet (CType {{suc<}}) c1 c2 pfc pfv = pure (oCodeMeet self-1 c1 c2 reflp reflp)
meet (CCumul {{suc<}} c) x y pfc pfv = oMeet self-1 c x y reflp reflp
meet (CΠ dom cod) f g reflp reflp
  = liftFunDep λ x →
    cod (approx x) ∋ f x ⊓ g x
      By hide {arg = ≤ₛ-sucMono (≤ₛ-cocone _  ≤⨟ smax-≤R  )}
meet (CΣ dom cod) (xfst , xsnd) (yfst , ysnd) reflp reflp =
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
meet (C≡ c x y) (w1 ⊢ _ ≅ _) (w2 ⊢ _ ≅ _) reflp reflp = do
  let
    w = c ∋ w1 ⊓ w2
      approxBy hide {arg = ≤ₛ-refl}
  pure (w ⊢ x ≅ y)

meet (Cμ tyCtor c D x₁) x y pfc pfv = {!x y !}
