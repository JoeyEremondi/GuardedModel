
-- Implementation of the meet on codes, assuming we have meet, cast, etc. for smaller types


open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Vec
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

open import ApproxExact
open import InductiveCodes
open import Sizes
-- open import CodePair

open import CastComp.Interface

module CastComp.DescMeet {{dt : DataTypes}} {{dg : DataGerms}} {{ic : CodesForInductives}}
    (⁇Allowed : Bool) {ℓ} (csize : Size) (scm : SmallerCastMeet ℓ ⁇Allowed csize)

  where

open import Code
open import Head
open import Util

open SmallerCastMeet scm





descMeet : ∀ {cB1 cB2 cBTarget : ℂ ℓ} { skel oTop}
      → (D1 : ℂDesc  cB1 skel)
      → (D2 : ℂDesc  cB2 skel)
      → (lto : oTop <ₛ csize )
      → (ltB : (codeSize cBTarget ≤ₛ smax  (codeSize cB1)  (codeSize cB2)))
      → (lt : smax ( (descSize D1) ) ( (descSize D2)) ≤ₛ  oTop)
      → ℂDesc cBTarget skel
descMeet  CEnd CEnd  lto ltB lt  = CEnd
descMeet {cB1 = cB1} {cB2} {cBTarget = cB} {oTop = oTop} (CArg c1 ar1 D1 _ reflp) (CArg c2 ar2 D2 _ reflp) lto ltB lt =
      CArg
        cRet
        (λ b → oCodeMeetArity (self _) (c1 (cb1 b)) (c2 (cb2 b)) reflp (ar1 (cb1 b)) (ar2 (cb2 b)))
        (descMeet D1 D2
          lto
          ltcB
          (smax-mono
              (≤suc (smax*-≤-n (FLit 1)) )
              (≤suc (smax*-≤-n (FLit 1)) )
            ≤⨟ lt)
          )
        _
        reflp
      module DescMeetArg where
        ltB12 :  smax (codeSize cB1) (codeSize cB2) ≤ₛ  oTop
        ltB12 =
          smax-mono
            (≤suc (≤suc smax-≤L ≤⨟ smax*-≤-n (FLit 2)))
            (≤suc (≤suc smax-≤L ≤⨟ smax*-≤-n (FLit 2)))
          ≤⨟ lt
        -- smax-mono
        --       (≤suc (≤suc smax-≤L ≤⨟ smax*-≤-n Fin.zero) )
        --       (≤suc (≤suc smax-≤L ≤⨟ smax*-≤-n Fin.zero) )
        --   ≤⨟ lt
        cb1 : ApproxEl cB → ApproxEl cB1
        cb1 cb =
          ⟨ cB1 ⇐ cB ⟩ cb
                approxBy Decreasing ≤< (smax-lub (ltB ≤⨟ ltB12) (smax-≤L ≤⨟ ltB12)) lto
        cb2 : _ → _
        cb2 cb =
          ⟨ cB2 ⇐ cB ⟩ cb
                approxBy Decreasing ( (≤< (smax-lub
                  (ltB
                  ≤⨟ ltB12)
                  ( smax-≤R
                  ≤⨟ ltB12)) lto) )
        cRet : ApproxEl cB → ℂ ℓ
        cRet cb =
          c1 (cb1 cb) ⊓ c2 (cb2 cb)
            By Decreasing   ≤<
              (smax-mono
                (≤↑ (codeSize (c1 (cb1 cb))) ≤⨟ ≤ₛ-sucMono (≤ₛ-cocone  (cb1 cb)  ≤⨟ smax*-≤-n (FLit 0)))
                (≤↑ (codeSize (c2 (cb2 cb))) ≤⨟ ≤ₛ-sucMono (≤ₛ-cocone  _  ≤⨟ smax*-≤-n (FLit 0)))
              ≤⨟ lt)
              lto
        ltcB = smax-sucMono (smax-mono
          ltB
          ((≤ₛ-limiting  λ cb → (_ ⊓Size _ By hide ≤⨟ ≤ₛ-cocone  (cb2 cb)) ≤⨟ ≤ₛ-cocone  (cb1 cb) )  ≤⨟ smax-lim2L (λ x → codeSize (c1 x)) (λ x → codeSize (c2 x))) -- (≤ₛ-limiting  {c = cB} _ λ cb → {!!} ≤⨟  _ ⊓Size _ By hide  )
          ≤⨟ smax-swap4)
descMeet {cB1 = cB1} {cB2 = cB2} {cBTarget = cB} {oTop = oTop} (CRec c1 ar1 D1 _ reflp) (CRec c2 ar2 D2 _ reflp) lto ltB lt  =
      CRec
        cRet
        (λ b → oNestedΣArity (self _) (c1 (cb1 b)) (c2 (cb2 b)) reflp (ar1 (cb1 b)) (ar2 (cb2 b)))
        (descMeet D1 D2 lto ltB ltcB) --(descMeet D1 D2 lto ltB ltcB)
        -- (λ cb k → fromL ([ Approx ] I1 ,, I2 ∋ j1 (cb1 cb) (fst (k12 cb k)) ⊓ j2 (cb2 cb) (snd (k12 cb k)) By hide {arg = ≤< ltI lto }))
        _ reflp
      module DescMeetHRec where
        ltB12 :  smax  (codeSize cB1)  (codeSize cB2) ≤ₛ  oTop
        ltB12 = smax-mono
          (≤suc ((≤suc ( smax-≤L)) ≤⨟ smax*-≤-n (FLit 2)))
          (≤suc ((≤suc ( smax-≤L)) ≤⨟ smax*-≤-n (FLit 2)))
          ≤⨟ lt
        cb1 : _ → _
        cb1 cb = ⟨ cB1 ⇐ cB ⟩ cb
              approxBy Decreasing
                ( ( ≤< (smax-lub
                  (ltB ≤⨟ ltB12)
                  (smax-≤L ≤⨟ ltB12 )) lto  ))
        cb2 : _ → _
        cb2 cb = ⟨ cB2 ⇐ cB ⟩ cb
              approxBy Decreasing
                ( ≤< (smax-lub
                  (ltB ≤⨟ ltB12)
                  (smax-≤R ≤⨟ ltB12 )) lto  )
        ltcB =
          smax-mono
            ( ≤suc (smax*-≤-n (FLit 1)))
            ( ≤suc (smax*-≤-n (FLit 1)))
            ≤⨟ lt
        ltCone1 : ∀ cb →  (codeSize (c1 (cb1 cb))) ≤ₛ
                           descSize (CRec c1 ar1 D1 (CΣ cB1 c1) reflp)
        ltCone1 cb = ≤suc (≤ₛ-cocone  _ ≤⨟ smax*-≤-n (FLit 0))
        ltCone2 : ∀ cb →  (codeSize (c2 (cb2 cb))) ≤ₛ
                           descSize (CRec c2 ar2 D2 (CΣ cB2 c2) reflp)
        ltCone2 cb = ≤suc (≤ₛ-cocone  _ ≤⨟ smax*-≤-n (FLit 0))
        cRet : ApproxEl cB → ℂ ℓ
        cRet cb = c1 (cb1 cb) ⊓ c2 (cb2 cb)
          By hide {arg = ≤<
            (smax-mono
              (≤suc (≤ₛ-cocone  _  ≤⨟ smax*-≤-n (FLit 0) ))
              (≤suc (≤ₛ-cocone  _  ≤⨟ smax*-≤-n (FLit 0) ))
            ≤⨟ lt)
            lto }
        k12 : ∀ cb → ApproxEl (cRet cb) → ApproxEl (c1 (cb1 cb)) × ApproxEl (c2 (cb2 cb))
        k12 cb k =  ⟨ (c1 (cb1 cb)) , (c2 (cb2 cb)) ⇐⊓⟩ k
          approxBy Decreasing
            ≤<
              (smax-mono (ltCone1 cb) (ltCone2 cb)
              ≤⨟ lt)
              lto
