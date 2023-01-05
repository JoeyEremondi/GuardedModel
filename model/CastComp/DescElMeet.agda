


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
      → (x : ⟦ interpDesc D b1 ⟧F (W̃ (Arg (λ d → interpDesc (E d) Gtt))) tt )
      → (y : ⟦ interpDesc D b2 ⟧F (W̃ (Arg (λ d → interpDesc (E d) Gtt))) tt )
      → (lto : oTop <ₛ cSize)
      → (ltB : codeSize cB ≤ₛ oTop)
      → let b12 = cB ∋ b1 ⊓ b2 approxBy Decreasing ≤< ltB lto
        in LÆ (⟦ interpDesc D b12 ⟧F (W̃ (Arg (λ d → interpDesc (E d) Gtt))) tt)
descMuMeet : ∀ {{æ : Æ}} {tyCtor : CName} {oTop : Size}
      → (Ds : DCtors ℓ tyCtor)
      → (x y : W̃ (Arg (λ d → interpDesc (Ds d) Gtt)) tt  )
      → (lto : oTop <ₛ cSize)
      → (lto' : S1 ≤ₛ oTop)
      → LÆ (W̃ (Arg (λ d → interpDesc (Ds d) Gtt)) tt  )
descMuMeet Ds W℧ y lto lto' = pure W℧
descMuMeet Ds x W℧ lto lto' = pure W℧
descMuMeet Ds W⁇ y lto lto' = pure y
descMuMeet Ds x W⁇ lto lto' = pure x
descMuMeet Ds (Wsup (FC (d , com1) resp1)) (Wsup (FC (d2 , com2) resp2)) lto lto' with decFin d d2
... | no neq = pure W℧
... | yes reflp = do
  (FC comRet respRet) ← descElMeet (Ds d) Ds Gtt Gtt (FC com1 resp1) (FC com2 resp2) lto lto'
  pure (Wsup (FC (d , {!!}) {!!}))

-- -- descElMeet CEnd E b1 b2 ElEnd ElEnd lto ltB = pure ElEnd
-- -- descElMeet {{æ }} (CArg c x D .(CΣ _ c) .reflp) E b1 b2 (ElArg a1 rest1) (ElArg a2 rest2) lto ltB  = do
-- --   let b12 = _ ∋ b1 ⊓ b2 approxBy Decreasing {!!}
-- --   a1-12 ← {!!} -- ⟨_⇐_⟩_By_ {{æ = æ}} (c b1) (c b12) a1 (Decreasing ?)
-- --   -- a2-12 ← ⟨ c b12 ⇐ c b2 ⟩ a2 By Decreasing {!!}
-- --   -- a1⊓a2 ← c b12 ∋ a1-12 ⊓ a2-12 By Decreasing {!!}
-- --   -- rest ← descElMeet D E (b1 , approx {{æ = _}} a1) (b2 , approx {{æ = _}} a2) rest1 rest2 {!!} {!!}
-- --   -- pure (ElArg a1⊓a2 (transport {!!} rest))
-- --   pure {!!}
-- -- -- descElMeet (CRec c x D .(CΣ _ c) .reflp) E b1 b2 (ElRec f1 rest1) (ElRec f2 rest2) lto ltB = do
-- -- --   f12 ← liftFun λ x → do
-- -- --     x1 ← ⟨ c b1 ⇐ c (_ ∋ b1 ⊓ b2 approxBy Decreasing _) ⟩ x By {!!}
-- -- --     x2 ← ⟨ c b2 ⇐ c (_ ∋ b1 ⊓ b2 approxBy Decreasing _) ⟩ x By {!!}
-- -- --     descMuMeet E (f1 x1) (f2 x2) lto
-- -- --   rest ← descElMeet D E b1 b2 rest1 rest2 {!!} {!!}
-- -- --   pure (ElRec f12 rest)
