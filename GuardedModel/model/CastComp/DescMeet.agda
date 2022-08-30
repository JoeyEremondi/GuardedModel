
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

module CastComp.DescMeet {{dt : DataTypes}} {{dg : DataGerms}} {{ic : InductiveCodes}} {{dgs : DataGermsSmaller}}
    {ℓ} (cSize : Ord) (vSize : Ord) (scm : SmallerCastMeet ℓ cSize vSize)

  where

open import Code
open import Head
open import Util


open SmallerCastMeet scm


{-# DISPLAY SmallerCastMeet._⊓_By_  = _⊓_By_  #-}
{-# DISPLAY SmallerCastMeet._∋_⊓_By_  = _∋_⊓_By_  #-}






descMeet : ∀ {I1 I2 cB1 cB2 cBTarget skel oTop}
      → (D1 : ℂDesc I1 cB1 skel)
      → (D2 : ℂDesc I2 cB2 skel)
      → (lto : omax∞ oTop <o cSize )
      → (ltI : omax (omax∞ (codeSize I1) ) (omax∞ (codeSize I2)) ≤o omax∞ oTop)
      → (ltB : (codeSize cBTarget ≤o omax  (codeSize cB1)  (codeSize cB2)))
      → (lt : omax ( (descSize D1) ) ( (descSize D2)) ≤o omax∞ oTop)
      → ℂDesc (I1 ⊓ I2 By hide {arg = ≤∘<-in-< (omax-mono (omax∞-self _) (omax∞-self _) ≤⨟ ltI) lto}) cBTarget skel
descMeet {I1 = I1} {I2} (CEnd i) (CEnd i₁)  lto ltI ltB lt  =
      CEnd (fromL ([ Approx ] I1 ,, I2 ∋ i ⊓ i₁ By hide {arg = ≤∘<-in-< ltI lto}))
descMeet {cB1 = cB1} {cB2} {cBTarget = cB} {oTop = oTop} (CArg c1 D1 _ reflp) (CArg c2 D2 _ reflp) lto ltI ltB lt =
      CArg
        cRet
        (descMeet D1 D2
          lto
          ltI
          ltcB
          (omax-mono
              (≤↑ _ ≤⨟ ≤o-sucMono (omax*-≤-n (Fin.suc (Fin.suc Fin.zero))) )
              (≤↑ _ ≤⨟ ≤o-sucMono (omax*-≤-n (Fin.suc (Fin.suc Fin.zero))) )
            ≤⨟ lt)
          -- (omax-mono (≤↑ _ ≤⨟ ≤o-sucMono (omax-≤R ≤⨟ omax-≤R)) (≤↑ _ ≤⨟ ≤o-sucMono (omax-≤R ≤⨟ omax-≤R)) ≤⨟ {!!})
          -- (≤∘<-in-< (omax-mono (≤↑ (descSize D1) ≤⨟ ≤o-sucMono omax-≤R) (≤↑ (descSize D2) ≤⨟ ≤o-sucMono omax-≤R))
          )
        _
        reflp
      where
        ltB12 :  omax (codeSize cB1) (codeSize cB2) ≤o omax∞ oTop
        ltB12 = omax-mono
              (≤↑ _ ≤⨟ ≤o-sucMono (≤↑ _ ≤⨟ ≤o-sucMono (omax∞-self _ ≤⨟ omax-≤L) ≤⨟ omax*-≤L ))
              (≤↑ _ ≤⨟ ≤o-sucMono (≤↑ _ ≤⨟ ≤o-sucMono (omax∞-self _ ≤⨟ omax-≤L) ≤⨟ omax*-≤L ))
          ≤⨟ lt
        -- ltB12 = omax-mono
        --       (≤↑ _ ≤⨟ ≤o-sucMono ((≤↑ _ ≤⨟ ≤o-sucMono (omax∞-self _ ≤⨟ omax-≤L)) ≤⨟ omax-≤L))
        --       (≤↑ _ ≤⨟ ≤o-sucMono ((≤↑ _ ≤⨟ ≤o-sucMono (omax∞-self _ ≤⨟ omax-≤L)) ≤⨟ omax-≤L))
        --        ≤⨟ lt
        cb1 : _ → _
        cb1 cb = fromL ([ Approx ]⟨ cB1 ⇐ cB ⟩ cb
              By hide {arg = ≤∘<-in-< (omax∞-lub
                (ltB
                ≤⨟ ltB12)
                ( omax-≤L
                ≤⨟ ltB12)) lto  })
        cb2 : _ → _
        cb2 cb = fromL ([ Approx ]⟨ cB2 ⇐ cB ⟩ cb
              By hide {arg = ≤∘<-in-< (omax∞-lub
                (ltB
                ≤⨟ ltB12)
                ( omax-≤R
                ≤⨟ ltB12)) lto  })
        ltcB = omax-sucMono (omax-mono
          (omax∞-mono ltB ≤⨟ omax∞-distR)
          (omax∞-mono ((≤o-limiting {{æ = Approx}} _ λ cb → ≤o-cocone ⦃ æ = Approx ⦄ _ (cb1 cb) (≤o-cocone ⦃ æ = Approx ⦄ _ (cb2 cb) (omax∞-mono (_ ⊓Size _ By hide) ≤⨟ omax∞-distR))) ≤⨟ omax-lim2L _ _ ) ≤⨟ omax∞-distR)
          ≤⨟ omax-swap4)
        -- ltcB = (omax-sucMono (omax-mono
        --     (omax∞-mono ltB ≤⨟ omax∞-distR)
        --     ((≤o-limiting {{æ = Approx}} _ λ cb → ≤o-cocone ⦃ æ = Approx ⦄ _ (cb1 cb) (≤o-cocone ⦃ æ = Approx ⦄ _ (cb2 cb)
        --       (omax∞-mono (c1 (cb1 cb) ⊓Size c2 (cb2 cb) By hide) ≤⨟ omax∞-distR))) ≤⨟ omax-lim2L _ _) ≤⨟ omax-swap4 ))
        cRet : ApproxEl cB → ℂ ℓ
        cRet cb = c1 (cb1 cb) ⊓ c2 (cb2 cb)
          By hide {arg = ≤∘<-in-<
            (omax-mono
              (≤↑ _ ≤⨟ ≤o-sucMono (≤o-cocone ⦃ æ = Approx ⦄ _ (cb1 cb) (omax∞-self _) ≤⨟ omax*-≤-n (Fin.suc Fin.zero)))
              (≤↑ _ ≤⨟ ≤o-sucMono (≤o-cocone ⦃ æ = Approx ⦄ _ (cb2 cb) (omax∞-self _) ≤⨟ omax*-≤-n (Fin.suc Fin.zero)))
            ≤⨟ lt)
            lto}
descMeet {I1 = I1} {I2 = I2} (CRec j1 D1) (CRec j2 D2) lto ltI ltB lt  =
      CRec
        (fromL ([ Approx ] I1 ,, I2 ∋ j1 ⊓ j2 By hide {arg = ≤∘<-in-< ltI lto }))
        (descMeet D1 D2 lto ltI ltB (omax-mono (≤↑ _) (≤↑ _) ≤⨟ lt))
descMeet {I1 = I1} {I2} {cB1 = cB1} {cB2 = cB2} {cBTarget = cB} {oTop = oTop} (CHRec c1 j1 D1 _ reflp) (CHRec c2 j2 D2 _ reflp) lto ltI ltB lt  =
      CHRec
        cRet
        (λ cb k → fromL ([ Approx ] I1 ,, I2 ∋ j1 (cb1 cb) (fst (k12 cb k)) ⊓ j2 (cb2 cb) (snd (k12 cb k)) By hide {arg = ≤∘<-in-< ltI lto }))
        (descMeet D1 D2 lto ltI ltB ltcB)
        _ reflp
      where
        --TODO need to add copy of cB to desc
        ltB12 :  omax  (codeSize cB1)  (codeSize cB2) ≤o omax∞ oTop
        ltB12 = omax-mono
          (≤↑ _ ≤⨟ ≤o-sucMono ((≤↑ _ ≤⨟ ≤o-sucMono (omax∞-self _ ≤⨟ omax-≤L)) ≤⨟ omax*-≤L))
          (≤↑ _ ≤⨟ ≤o-sucMono ((≤↑ _ ≤⨟ ≤o-sucMono (omax∞-self _ ≤⨟ omax-≤L)) ≤⨟ omax*-≤L))
          -- (≤↑ _ ≤⨟ ≤o-sucMono ( omax∞-self _ ≤⨟ omax-≤L ≤⨟ ≤↑ _ ≤⨟  omax-≤L ))
          -- (≤↑ _ ≤⨟ ≤o-sucMono ( omax∞-self _ ≤⨟ omax-≤L ≤⨟ ≤↑ _ ≤⨟  omax-≤L ))
          ≤⨟ lt
        cb1 : _ → _
        cb1 cb = fromL ([ Approx ]⟨ cB1 ⇐ cB ⟩ cb
              By hide {arg = ≤∘<-in-< (omax∞-lub
                (ltB ≤⨟ ltB12)
                (omax-≤L ≤⨟ ltB12 )) lto  })
        cb2 : _ → _
        cb2 cb = fromL ([ Approx ]⟨ cB2 ⇐ cB ⟩ cb
              By hide {arg = ≤∘<-in-< (omax∞-lub
                (ltB ≤⨟ ltB12)
                (omax-≤R ≤⨟ ltB12 )) lto  })
        ltcB =
          omax-mono
            ( ≤↑ _ ≤⨟ ≤o-sucMono (omax*-≤-n (Fin.suc (Fin.suc Fin.zero))))
            ( ≤↑ _ ≤⨟ ≤o-sucMono (omax*-≤-n (Fin.suc (Fin.suc Fin.zero))))
            ≤⨟ lt
        ltCone1 : ∀ cb → omax∞ (codeSize (c1 (cb1 cb))) ≤o
                           descSize (CHRec c1 j1 D1 (CΣ cB1 c1) reflp)
        ltCone1 cb = ≤↑ _ ≤⨟ ≤o-sucMono (≤o-cocone {{æ = Approx}} _ _ (≤o-refl _) ≤⨟ omax*-≤-n (Fin.suc Fin.zero))
        -- (≤o-cocone ⦃ æ = Approx ⦄ _ (cb1 cb) (≤o-refl _) ≤⨟ omax-≤L ≤⨟ omax-≤R ≤⨟ ≤↑ _)
        ltCone2 : ∀ cb → omax∞ (codeSize (c2 (cb2 cb))) ≤o
                           descSize (CHRec c2 j2 D2 (CΣ cB2 c2) reflp)
        ltCone2 cb = ≤↑ _ ≤⨟ ≤o-sucMono (≤o-cocone {{æ = Approx}} _ _ (≤o-refl _) ≤⨟ omax*-≤-n (Fin.suc Fin.zero))
        --(≤o-cocone ⦃ æ = Approx ⦄ _ (cb2 cb) (≤o-refl _) ≤⨟ omax-≤L ≤⨟ omax-≤R ≤⨟ ≤↑ _)
        cRet : ApproxEl cB → ℂ ℓ
        cRet cb = c1 (cb1 cb) ⊓ c2 (cb2 cb)
          By hide {arg = ≤∘<-in-<
            (omax-mono
              (≤↑ _ ≤⨟ ≤o-sucMono (≤o-cocone {{æ = Approx}} _ _ (omax∞-self _) ≤⨟ omax*-≤-n (Fin.suc Fin.zero)))
              (≤↑ _ ≤⨟ ≤o-sucMono (≤o-cocone {{æ = Approx}} _ _ (omax∞-self _) ≤⨟ omax*-≤-n (Fin.suc Fin.zero)))
            ≤⨟ lt)
            --(omax-mono (omax∞-self _ ≤⨟ ltCone1 cb) (omax∞-self _ ≤⨟ ltCone2 cb) ≤⨟ lt)
            lto }
        k12 : ∀ cb → ApproxEl (cRet cb) → ApproxEl (c1 (cb1 cb)) × ApproxEl (c2 (cb2 cb))
        k12 cb k = fromL ([ Approx ]⟨ (c1 (cb1 cb)) , (c2 (cb2 cb)) ⇐⊓⟩ k
          By hide {arg = ≤∘<-in-<
            (omax-mono (ltCone1 cb) (ltCone2 cb)
            ≤⨟ lt)
            -- (omax-mono
            -- (ltCone1 cb)
            -- (ltCone2 cb)
            -- ≤⨟ lt)
            lto})
