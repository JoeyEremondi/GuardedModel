
-- Implementation of the meet on codes, assuming we have meet, cast, etc. for smaller types


open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Equality
open import UnkGerm
open import GuardedAlgebra
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude

open import ApproxExact
open import InductiveCodes
-- open import CodePair
open import SizeOrd

open import CastComp.Interface

module CastComp.DescMeet {{dt : DataTypes}} {{dg : DataGerms}} {{ic : InductiveCodes}}
    (⁇Allowed : ⁇Flag) {ℓ} (size : Size) (scm : SmallerCastMeet ⁇Allowed ℓ size)

  where

open import Code
open import Head
open import Util

open SmallerCastMeet scm


{-# DISPLAY SmallerCastMeet._⊓_By_  = _⊓_By_  #-}
{-# DISPLAY SmallerCastMeet._∋_⊓_By_  = _∋_⊓_By_  #-}



open import Assumption


descMeet : ∀ {I1 I2 cB1 cB2 cBTarget skel oTop}
      → {@(tactic assumption) np : notPos ⁇Allowed}
      → (D1 : ℂDesc I1 cB1 skel)
      → (D2 : ℂDesc I2 cB2 skel)
      → (lto : oTop <ₛ size )
      → (ltI : smax ( (codeSize I1) ) ( (codeSize I2)) ≤ₛ  oTop)
      → (ltB : (codeSize cBTarget ≤ₛ smax  (codeSize cB1)  (codeSize cB2)))
      → (lt : smax ( (descSize D1) ) ( (descSize D2)) ≤ₛ  oTop)
      → ℂDesc (I1 ⊓ I2 By hide {arg = ≤< ltI lto}) cBTarget skel
descMeet {I1 = I1} {I2} (CEnd i) (CEnd i₁)  lto ltI ltB lt  =
      CEnd (fromL ([ Approx ] I1 ,, I2 ∋ i ⊓ i₁ By hide {arg = ≤< ltI lto}))
descMeet {cB1 = cB1} {cB2} {cBTarget = cB} {oTop = oTop} (CArg c1 D1 _ reflp) (CArg c2 D2 _ reflp) lto ltI ltB lt =
      CArg
        cRet
        (descMeet D1 D2
          lto
          ltI
          ltcB
          (smax-mono
              (≤suc (smax*-≤-n (Fin.suc (Fin.suc Fin.zero))) )
              (≤suc (smax*-≤-n (Fin.suc (Fin.suc Fin.zero))) )
            ≤⨟ lt)
          )
        _
        reflp
      module DescMeetArg where
        ltB12 :  smax (codeSize cB1) (codeSize cB2) ≤ₛ  oTop
        ltB12 = smax-mono
              (≤suc (≤suc smax-≤L ≤⨟ smax*-≤-n Fin.zero) )
              (≤suc (≤suc smax-≤L ≤⨟ smax*-≤-n Fin.zero) )
          ≤⨟ lt
        cb1 : ApproxEl cB → ApproxEl cB1
        cb1 cb = fromL ([ Approx ]⟨ cB1 ⇐ cB ⟩ cb
              By (argNotPos (≤< (smax-lub (ltB ≤⨟ ltB12) (smax-≤L ≤⨟ ltB12)) lto)) )
        cb2 : _ → _
        cb2 cb =  fromL ([ Approx ]⟨ cB2 ⇐ cB ⟩ cb
              By (argNotPos (≤< (smax-lub
                (ltB
                ≤⨟ ltB12)
                ( smax-≤R
                ≤⨟ ltB12)) lto) ))
        cRet : ApproxEl cB → ℂ ℓ
        cRet cb =  c1 (cb1 cb) ⊓ c2 (cb2 cb)
          By (hide {arg =  ≤<
            (smax-mono
              (≤↑ (codeSize (c1 (cb1 cb))) ≤⨟ ≤ₛ-sucMono (≤ₛ-cocone ⦃ æ = Approx ⦄ (cb1 cb)  ≤⨟ smax*-≤-n (Fin.suc Fin.zero)))
              (≤↑ (codeSize (c2 (cb2 cb))) ≤⨟ ≤ₛ-sucMono (≤ₛ-cocone {{æ = Approx}} _  ≤⨟ smax*-≤-n (Fin.suc Fin.zero)))
            ≤⨟ lt)
            lto} )
        ltcB = smax-sucMono (smax-mono
          ltB
          ((≤ₛ-limiting {{æ = Approx}} λ cb → (_ ⊓Size _ By hide ≤⨟ ≤ₛ-cocone {{æ = Approx}} (cb2 cb)) ≤⨟ ≤ₛ-cocone {{æ = Approx}} (cb1 cb) )  ≤⨟ smax-lim2L (λ x → codeSize (c1 x)) (λ x → codeSize (c2 x))) -- (≤ₛ-limiting ⦃ æ = Approx ⦄ {c = cB} _ λ cb → {!!} ≤⨟  _ ⊓Size _ By hide  )
          ≤⨟ smax-swap4)
descMeet {I1 = I1} {I2 = I2} (CRec j1 D1) (CRec j2 D2) lto ltI ltB lt  =
      CRec
        (fromL ([ Approx ] I1 ,, I2 ∋ j1 ⊓ j2 By hide {arg = ≤< ltI lto }))
        (descMeet D1 D2 lto ltI ltB (smax-mono (≤↑ _) (≤↑ _) ≤⨟ lt))
descMeet {I1 = I1} {I2} {cB1 = cB1} {cB2 = cB2} {cBTarget = cB} {oTop = oTop} (CHRec c1 j1 D1 _ reflp) (CHRec c2 j2 D2 _ reflp) lto ltI ltB lt  =
      CHRec
        cRet
        (λ cb k → fromL ([ Approx ] I1 ,, I2 ∋ j1 (cb1 cb) (fst (k12 cb k)) ⊓ j2 (cb2 cb) (snd (k12 cb k)) By hide {arg = ≤< ltI lto }))
        (descMeet D1 D2 lto ltI ltB ltcB)
        _ reflp
      module DescMeetHRec where
        ltB12 :  smax  (codeSize cB1)  (codeSize cB2) ≤ₛ  oTop
        ltB12 = smax-mono
          (≤suc ((≤suc ( smax-≤L)) ≤⨟ smax*-≤L))
          (≤suc ((≤suc ( smax-≤L)) ≤⨟ smax*-≤L))
          ≤⨟ lt
        cb1 : _ → _
        cb1 cb = fromL ([ Approx ]⟨ cB1 ⇐ cB ⟩ cb
              By (argNotPos ( ≤< (smax-lub
                (ltB ≤⨟ ltB12)
                (smax-≤L ≤⨟ ltB12 )) lto  )))
        cb2 : _ → _
        cb2 cb = fromL ([ Approx ]⟨ cB2 ⇐ cB ⟩ cb
              By argNotPos ( ≤< (smax-lub
                (ltB ≤⨟ ltB12)
                (smax-≤R ≤⨟ ltB12 )) lto  ))
        ltcB =
          smax-mono
            ( ≤suc (smax*-≤-n (Fin.suc (Fin.suc Fin.zero))))
            ( ≤suc (smax*-≤-n (Fin.suc (Fin.suc Fin.zero))))
            ≤⨟ lt
        ltCone1 : ∀ cb →  (codeSize (c1 (cb1 cb))) ≤ₛ
                           descSize (CHRec c1 j1 D1 (CΣ cB1 c1) reflp)
        ltCone1 cb = ≤suc (≤ₛ-cocone {{æ = Approx}} _ ≤⨟ smax*-≤-n (Fin.suc Fin.zero))
        ltCone2 : ∀ cb →  (codeSize (c2 (cb2 cb))) ≤ₛ
                           descSize (CHRec c2 j2 D2 (CΣ cB2 c2) reflp)
        ltCone2 cb = ≤suc (≤ₛ-cocone {{æ = Approx}} _ ≤⨟ smax*-≤-n (Fin.suc Fin.zero))
        cRet : ApproxEl cB → ℂ ℓ
        cRet cb = c1 (cb1 cb) ⊓ c2 (cb2 cb)
          By hide {arg = ≤<
            (smax-mono
              (≤suc (≤ₛ-cocone {{æ = Approx}} _  ≤⨟ smax*-≤-n (Fin.suc Fin.zero)))
              (≤suc (≤ₛ-cocone {{æ = Approx}} _  ≤⨟ smax*-≤-n (Fin.suc Fin.zero)))
            ≤⨟ lt)
            lto }
        k12 : ∀ cb → ApproxEl (cRet cb) → ApproxEl (c1 (cb1 cb)) × ApproxEl (c2 (cb2 cb))
        k12 cb k = fromL ([ Approx ]⟨ (c1 (cb1 cb)) , (c2 (cb2 cb)) ⇐⊓⟩ k
          By hide {arg = ≤<
            (smax-mono (ltCone1 cb) (ltCone2 cb)
            ≤⨟ lt)
            lto})
