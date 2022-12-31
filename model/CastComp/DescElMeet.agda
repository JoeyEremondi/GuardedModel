


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

module CastComp.DescElMeet {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ} (cSize : Size) (vSize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed cSize vSize)

  where

open import Head
open import Util
open import GTypes

open import W

open SmallerCastMeet scm
open import WMuConversion


open import Code


descElMeet : ∀ {{æ : Æ}} {cB : ℂ ℓ} {tyCtor : CName} { skel oTop}
      → (D : ℂDesc  cB skel)
      → (E : DCtors ℓ tyCtor)
      → (b1 b2 : ApproxEl cB)
      → (x : ℂDescEl D (ℂμ tyCtor E) b1 )
      → (y : ℂDescEl D (ℂμ tyCtor E) b2 )
      → (lto : oTop <ₛ cSize)
      → (ltB : codeSize cB ≤ₛ oTop)
      → LÆ (ℂDescEl D (ℂμ tyCtor E) (cB ∋ b1 ⊓ b2 approxBy Decreasing ≤< ltB lto))
descMuMeet : ∀ {{æ : Æ}}  {tyCtor oTop}
      → (Ds : DCtors ℓ tyCtor)
      → (x y : ℂμ tyCtor  Ds  )
      → (lto : oTop <ₛ cSize)
      → LÆ (ℂμ tyCtor  Ds )
descMuMeet Ds Cμ⁇ y ltB = pure y
descMuMeet Ds x Cμ⁇ ltB = pure x
descMuMeet Ds x Cμ℧ ltB = pure Cμ℧
descMuMeet Ds Cμ℧ y ltB = pure Cμ℧
descMuMeet Ds (Cinit d1 x) (Cinit d2 y) lto with decFin d1 d2
... | no npf = pure Cμ℧
... | yes reflp = do
  elRet ← descElMeet (Ds d1) Ds Gtt Gtt x y lto {!!}
  pure (Cinit d1 (transport {!!} elRet))

descElMeet CEnd E b1 b2 ElEnd ElEnd lto ltB = pure ElEnd
descElMeet {{æ }} (CArg c x D .(CΣ _ c) .reflp) E b1 b2 (ElArg a1 rest1) (ElArg a2 rest2) lto ltB  = do
  let b12 = _ ∋ b1 ⊓ b2 approxBy Decreasing {!!}
  a1-12 ← {!!} -- ⟨_⇐_⟩_By_ {{æ = æ}} (c b1) (c b12) a1 (Decreasing ?)
  -- a2-12 ← ⟨ c b12 ⇐ c b2 ⟩ a2 By Decreasing {!!}
  -- a1⊓a2 ← c b12 ∋ a1-12 ⊓ a2-12 By Decreasing {!!}
  -- rest ← descElMeet D E (b1 , approx {{æ = _}} a1) (b2 , approx {{æ = _}} a2) rest1 rest2 {!!} {!!}
  -- pure (ElArg a1⊓a2 (transport {!!} rest))
  pure {!!}
-- descElMeet (CRec c x D .(CΣ _ c) .reflp) E b1 b2 (ElRec f1 rest1) (ElRec f2 rest2) lto ltB = do
--   f12 ← liftFun λ x → do
--     x1 ← ⟨ c b1 ⇐ c (_ ∋ b1 ⊓ b2 approxBy Decreasing _) ⟩ x By {!!}
--     x2 ← ⟨ c b2 ⇐ c (_ ∋ b1 ⊓ b2 approxBy Decreasing _) ⟩ x By {!!}
--     descMuMeet E (f1 x1) (f2 x2) lto
--   rest ← descElMeet D E b1 b2 rest1 rest2 {!!} {!!}
--   pure (ElRec f12 rest)
