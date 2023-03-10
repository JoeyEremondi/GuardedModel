

{-# OPTIONS --cubical --guarded #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_β‘p_ ; reflp ; cong)
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
open import WMuEq

module CastComp {{_ : DataTypes}} {{_ : DataGerms}} {{_ : InductiveCodes}} {{_ : DataGermsSmaller}}  where

open import Code
open import Head
open import Util
open import Ord
-- open Ord β El β§ Cπ refl


open import Germ


record SizedCastMeet (β : β) (cSize vSize : Ord) : Set where
  field
    oβ : β {{_ : Γ}}  β (c : βwf β)
      β (pfc1 : wfSize c β‘p cSize )
      β ( pfv2 : OZ β‘p vSize )
      β (wfEl c)
    oMeet : β {{_ : Γ}}
      β (c : βwf β)
      β (x y : wfEl c)
      β ( pfc1 : (wfSize c)  β‘p cSize )
      β ( pfv1 : omax (wfElSize c x) (wfElSize c y)  β‘p vSize )
      β LΓ (wfEl c)

    oCodeMeet :
      (c1 c2 : βwf β)
      β ( pfc1 : (wfPairSize c1 c2)  β‘p cSize )
      β ( pfv1 : OZ  β‘p vSize )
      β (βwf β)

    oCast : β {{_ : Γ}}
      β (csource cdest : βwf β)
      β ( pfc1 : wfPairSize csource cdest  β‘p cSize)
      β  (x : wfEl csource)
      β ( pfv1 : wfElSize csource x β‘p vSize)
      -> LΓ ( wfEl cdest)

open SizedCastMeet


castMeetRec :  (β : β) β (cSize vSize : Ord)
      β (self : β {cs vs : Ord} β ((cs , vs) <oPair (cSize , vSize)) β SizedCastMeet β cs vs)
      β (βself : β {cs vs} {{ _ : 0< β }} β SizedCastMeet (predβ β) cs vs)
      β  SizedCastMeet β cSize vSize
castMeetRec β cSize vSize self βself = {!!} -- record
--                           -- { oβ = β ; oMeet = meet ; oToGerm = toGerm ; oFromGerm = fromGerm ; oToDataGerm = toDataGerm ; oFromDataGerm = fromDataGerm ; oCast = cast }
  where
    ----------------------------------------------------------------------------------------------------------
    -- Nicer interfaces to our "smaller" functions, so we don't have to muck around with quadruples of ordinals

    β : β {{_ : Γ}}  β (c : βwf β)
      β (_ : wfSize c β‘p cSize)
      β {{_ : O1  β‘p cSize }}
      β (wfEl c)
    β (Cβ |wf| _) reflp = ββ
    β (Cβ§ |wf| _) reflp = tt
    β (Cπ |wf| _) reflp = tt
    β (Cπ |wf| _) reflp = true
    β (CType β¦ suc< β¦ |wf| _) reflp = Cβ
    β (CΞ  dom cod |wf| (IWFΞ  wfdom wfcod)) reflp x =
      β (cod (approx x) |wf| wfcod (approx x))
        By (β€o-sucMono (β€o-trans (β€o-cocone {{Γ¦ = Approx}} _ (approx x) (β€o-refl _)) omax-β€R))
    β {{Γ¦}} (CΞ£ dom cod |wf| (IWFΞ£ wfdom wfcod)) reflp =
      let
        βx = withApprox Ξ» Γ¦ β β_By_ {{Γ¦}} (dom |wf| wfdom)
          (β€o-sucMono (β€o-trans (β€o-refl _) omax-β€L))
        βy = β (cod (approx βx) |wf| (wfcod (approx βx)))
          By (β€o-sucMono (β€o-trans (β€o-cocone {{Γ¦ = Approx}} _ (approx βx) (β€o-refl _)) omax-β€R))
      in βx , βy
    β (Cβ‘ c x y |wf| (IWFβ‘ wf)) reflp =
      let
        wit = fromL ([ Approx ] (c |wf| wf) β  x β y By (β€o-sucMono omax-β€L))
      in (wit β’ x β y)
    β (CΞΌ tyCtor c D x |wf| _) reflp = Wβ

    codeMeet : β {{_ : Γ}} {h1 h2}
      β (c1 c2 : β β )
      β IndWF c1 β IndWF c2
      β HeadMatchView h1 h2
      β h1 β‘p codeHead c1
      β h2 β‘p codeHead c2
      β (csize (codePairSize c1 c2) β‘p cSize)
      β (OZ β‘p vSize)
      β (β β)
    -- Error cases: the meet is β§ if either argument is β§
    -- or the heads don't match
    codeMeet _ c2 wf1 wf2 (Hβ§L reflp) eq1 eq2 reflp reflp = Cβ§
    codeMeet c1 _ wf1 wf2 (Hβ§R reflp) eq1 eq2 reflp reflp = Cβ§
    codeMeet c1 c2 wf1 wf2 (HNeq x) eq1 eq2 reflp reflp = Cβ§
    -- Meet of anything with β is that thing
    codeMeet _ c2 wf1 wf2 (HβL reflp xβ) eq1 eq2 reflp reflp = c2
    codeMeet c1 _ wf1 wf2 (HβR reflp) eq1 eq2 reflp reflp = c1
    -- Otherwise, we have two codes with the same head, so we take the meet of the parts
    -- after performing the required castsa
    codeMeet c1 c2 wf1 wf2 (HEq {h1 = h} reflp) eq1 eq2 reflp reflp = {!h c1 c2!}
--     -- If either is β§ or the heads don't match, the result is β§
--     codeMeet (c1 |wf| wf1) (c2 |wf| wf2) reflp reflp | h1  | h2  | Hβ§L reflp =  Cβ§ |wf| IWFβ§
--     codeMeet (c1 |wf| wf1) (c2 |wf| wf2) reflp reflp | h1  | h2  | Hβ§R x = Cβ§ |wf| IWFβ§
--     codeMeet (c1 |wf| wf1) (c2 |wf| wf2) reflp reflp | .(HStatic _)  | .(HStatic _)  | HNeq x = Cβ§ |wf| IWFβ§
--     -- If either is β, then the meet is just the other code
--     codeMeet (Cβ |wf| wf1) (c2 |wf| wf2) reflp reflp | h1  | h2  | HβL reflp xβ = c2 |wf| wf2
--     codeMeet (c1 |wf| wf1) (Cβ |wf| wf2) reflp reflp | .(HStatic _)  | h2  | HβR reflp = c1 |wf| wf1
--     -- Otherwise, we have two codes with the same head
--     -- Trivial cases with no arguments: both inputs are identical
--     codeMeet (Cπ |wf| wf1) (Cπ |wf| wf2) reflp reflp | HStatic Hπ  | .(HStatic Hπ)  | HEq reflp = Cπ |wf| IWFπ
--     codeMeet (Cπ |wf| wf1) (Cπ |wf| wf2) reflp reflp | HStatic Hπ  | .(HStatic Hπ)  | HEq reflp = Cπ |wf| IWFπ
--     codeMeet (CType {{suc<}} |wf| wf1) (CType |wf| wf2) reflp reflp | HStatic HType  | .(HStatic HType)  | HEq reflp = CType {{_}} {{_}} {{suc<}} |wf| IWFType
--     codeMeet (CΞ  dom1 cod1 |wf| (IWFΞ  domwf1 codwf1)) (CΞ  dom2 cod2 |wf| (IWFΞ  domwf2 codwf2)) reflp reflp | HStatic HΞ   | .(HStatic HΞ )  | HEq reflp
--       =
--         let
--           dom12 = (dom1 |wf| domwf1) β (dom2 |wf| domwf2)
--                         By β€o-sucMono omax-β€L
--           cod12 : (x : wfApproxEl dom12) β βwf β
--           cod12 x12 =
--             let
--               x1 = [ Approx ]β¨ dom1 |wf| domwf1 β dom12 β© x12 By β€o-sucMono omax-β€L
--               x2 = [ Approx ]β¨ dom2 |wf| domwf2 β dom12 β© x12 By {!!}
--             in
--               (cod1 (fromL x1) |wf| codwf1 _) β cod2 (fromL x2) |wf| codwf2 _
--                       By {!!}
--         in CΞ 
--           (code dom12)
--           {!Ξ» x β !}
--         |wf| {!!}
--     codeMeet (CΞ£ c1 cod |wf| wf1) (CΞ£ c2 codβ |wf| wf2) reflp reflp | HStatic HΞ£  | .(HStatic HΞ£)  | HEq reflp = {!!}
--     codeMeet (Cβ‘ c1 x y |wf| wf1) (Cβ‘ c2 xβ yβ |wf| wf2) reflp reflp | HStatic Hβ  | .(HStatic Hβ)  | HEq reflp = {!!}
--     codeMeet (CΞΌ tyCtor c1 D x |wf| wf1) (CΞΌ tyCtorβ c2 Dβ xβ |wf| wf2) reflp reflp | HStatic (HCtor xβ)  | .(HStatic (HCtor xβ))  | HEq reflp = {!!}

-- -- --     meet : β {{_ : Γ}}
-- -- --       β (c : βwf β)
-- -- --       β (x y : wfEl c)
-- -- --       β { pfc1 : (wfSize c)  β‘p cSize }
-- -- --       β {{ pfc2 : O1  β‘p cSize }}
-- -- --       β { (wfElSize c x)  β‘p vSize }
-- -- --       β { (wfElSize c y)  β‘p vSize }
-- -- --       β LΓ (wfEl c)
-- -- --     meet (c |wf| wf) x y with codeHead c in eqc
-- -- --     ... | ch with valueHead c eqc x in eq1 | valueHead c eqc y in eq2 | valHeadMatchView (valueHead c eqc x) (valueHead c eqc y)
-- -- --     -- If either arg is bottom or there is a head mismatch, produce error
-- -- --     ... |  h1 |  h2 |  VHβ§L xβ = pure (β§ c)
-- -- --     ... |  h1 |  h2 |  VHβ§R xβ = pure (β§ c)
-- -- --     ... |  .(HVInβ _ _) |  .(HVInβ _ _) |  VHNeqβ xβ = pure (β§ c)
-- -- --     ... |  .(HVal _) |  .(HVal _) |  VHNeq xβ = pure (β§ c)
-- -- --     -- If either is β, then return the other argument
-- -- --     ... |  h1 |  h2 |  VHβL xβ xβ = pure y
-- -- --     ... |  .(HVal _) |  h2 |  VHβR xβ = pure x
-- -- --     ... |  h1 |  h2 |  VHInβL xβ xβ = pure y
-- -- --     ... |  .(HVInβ _ _) |  h2 |  VHInβR xβ = pure x
-- -- --     -- Otherwise the head matches, so we do case-analysis on the type to see how to proceed
-- -- --     meet (Cπ |wf| _) true true {reflp} | .(HStatic _)  | .(HVal _)  | .(HVal _)  | VHEq reflp
-- -- --       = pure true
-- -- --     -- We have a special function for the meet of two types
-- -- --     meet (CType {{<suc}} |wf| _) x y | HStatic HType  | HVal h  | .(HVal _)  | VHEq reflp = {!!}
-- -- --     -- The meet of two functions is the function that takes the meet of the two arguments
-- -- --     meet (CΞ  dom cod |wf| (IWFΞ  domwf codwf)) f1 f2 {reflp} | .(HStatic _)  | .(HVal _)  | .(HVal _)  | VHEq reflp
-- -- --       = liftFunDep Ξ» x
-- -- --         β (cod (approx x) |wf| codwf (approx x)) β
-- -- --           (f1 x) β (f2 x)
-- -- --               By (β€o-sucMono (β€o-trans (β€o-cocone {{Γ¦ = Approx}} _ (approx  x) (β€o-refl _)) omax-β€R))
-- -- --     -- To take the meet of dependent pairs, we take the meet of the first elements
-- -- --     -- then cast the seconds to the codomain applied to the meet of the firsts
-- -- --     -- and take their meet
-- -- --     meet {{Γ¦Init}} (CΞ£ dom cod |wf| (IWFΞ£ domwf codwf )) (x1 , x2) (y1 , y2) {reflp} {pf2} | .(HStatic _)  | .(HVal _)  | .(HVal _)  | VHEq reflp = do
-- -- --       xy1 β withApproxL' Ξ» Γ¦ conv β
-- -- --         [ Γ¦ ] (dom |wf| domwf) β
-- -- --           (exact {{Γ¦}} (conv x1) ) β (exact {{Γ¦}} (conv y1))
-- -- --             By (β€o-sucMono omax-β€L)
-- -- --       x2cast β
-- -- --         β¨ cod (approx xy1) |wf| codwf (approx xy1) β (cod (approx x1) |wf| codwf (approx x1)) β© x2
-- -- --           By β€o-sucMono (β€o-trans (β€o-cocone β¦ Γ¦ = Approx β¦ _ (approx xy1) (β€o-refl _)) omax-β€R)
-- -- --       y2cast β
-- -- --         β¨ cod (approx xy1) |wf| codwf _ β cod (approx y1) |wf| codwf _ β© y2
-- -- --           By β€o-sucMono (β€o-trans (β€o-cocone β¦ Γ¦ = Approx β¦ _ (approx xy1) (β€o-refl _)) omax-β€R)
-- -- --       xy2 β  (cod (approx xy1) |wf| codwf _) β x2cast β y2cast
-- -- --           By β€o-sucMono (β€o-trans (β€o-cocone β¦ Γ¦ = Approx β¦ _ (approx xy1) (β€o-refl _)) omax-β€R)
-- -- --       pure (xy1 , xy2)
-- -- --     --Meet of two equality proofs is just the meet of their witnesses
-- -- --     meet (Cβ‘ c xβ yβ |wf| IWFβ‘ wf) (w1 β’ _ β _) (w2 β’ _ β _) {reflp} | .(HStatic _)  | .(HVal _)  | .(HVal _)  | VHEq reflp = do
-- -- --       w12 β [ Approx ] (c |wf| wf) β w1 β w2
-- -- --           By β€o-sucMono omax-β€L
-- -- --       pure (w12 β’ xβ β yβ)
-- -- --     meet (CΞΌ tyCtor c D xβ |wf| wf) x y | .(HStatic _)  | .(HVal _)  | .(HVal _)  | VHEq reflp = {!!}
-- -- --     ... |  .(HVInβ _ _) |  .(HVInβ _ _) |  VHEqβ xβ = {!!}


-- -- --     toGerm : β {{_ : Γ}}{ h} β (c : βwf β)
-- -- --       β  (pfc1 : O1 β‘p cSize)
-- -- --       β  (pfc2 : (wfSize c) β‘p cSize)
-- -- --       β codeHead (code c) β‘p HStatic h
-- -- --       β (x : wfEl c)
-- -- --       β (pfv1 : wfElSize c x β‘p vSize)
-- -- --       β  (pfv2 : O1 β‘p vSize)
-- -- --       β LΓ (germ h β)
-- -- --     fromGerm : β {{_ : Γ}}{ h} β (c : βwf β)
-- -- --       β (pfc1 : wfSize c β‘p cSize)
-- -- --       β  (pfc2 : O1 β‘p cSize)
-- -- --       β codeHead (code c) β‘p HStatic h
-- -- --       β (x : El {β} Cβ)
-- -- --       β  (pfv1 : elSize Cβ x β‘p vSize)
-- -- --       β  (pfv2 : O1 β‘p vSize)
-- -- --       β LΓ (wfEl c)

-- -- --     toDataGerm : β {{_ : Γ}} {cI : β β} (tyCtor : CName) (D : DName tyCtor β βDesc cI Cπ )
-- -- --       β {i : ApproxEl cI}
-- -- --       β {@(tactic default (reflp {A = Ord} {cSize})) pfc1 :  (codeSize (CΞΌ tyCtor cI D i))  β‘p cSize }
-- -- --       β {@(tactic default (reflp {A = Ord} {cSize})) pfc2 :  (dataGermDescSize β tyCtor)  β‘p cSize }
-- -- --       β (x : βΞΌ tyCtor D i)
-- -- --       β {@(tactic default (reflp {A = Ord} {vSize})) pfv1 : elSize (CΞΌ tyCtor cI D i) (transport βΞΌW x)  β‘p vSize }
-- -- --       β {@(tactic default (reflp {A = Ord} {vSize})) pfv2 : elSize (CΞΌ tyCtor cI D i) (transport βΞΌW x)  β‘p vSize }
-- -- --       β W (germContainer β tyCtor (βΉβ β)) (βTy β) tt

-- -- --     fromDataGerm : β {{_ : Γ}} {cI : β β} (tyCtor : CName) (D : DName tyCtor β βDesc cI Cπ )
-- -- --       β {i : ApproxEl cI}
-- -- --       β {@(tactic default (reflp {A = Ord} {cSize})) pfc1 :  (codeSize (CΞΌ tyCtor cI D i))  β‘p cSize }
-- -- --       β {@(tactic default (reflp {A = Ord} {cSize})) pfc2 :  (dataGermDescSize β tyCtor)  β‘p cSize }
-- -- --       β (x : W (germContainer β tyCtor (βΉβ β)) (βTy β) tt)
-- -- --       β {@(tactic default (reflp {A = Ord} {vSize})) pfv1 : O1  β‘p vSize }
-- -- --       β {@(tactic default (reflp {A = Ord} {vSize})) pfv2 : O1  β‘p vSize }
-- -- --       β (βΞΌ tyCtor D i)


-- -- --     cast : β {{_ : Γ}}
-- -- --       β (csource cdest : βwf β)
-- -- --       β (pfc1 :(wfSize cdest)  β‘p cSize)
-- -- --       β ( pfc2 :  (wfSize csource) β‘p cSize)
-- -- --       β  (x : wfEl csource)
-- -- --       β (pfv1 : wfElSize csource x β‘p vSize)
-- -- --       β (pfv2 : O1 β‘p vSize)
-- -- --       -> LΓ ( wfEl cdest)
-- -- --     cast (csource |wf| swf) (cdest |wf| dwf) reflp reflp x reflp reflp with  codeHead csource in eq1 | codeHead cdest in eq2 | headMatchView (codeHead csource) (codeHead cdest)
-- -- --     -- If either the source or target is error, or there is a head mismatch, we produce an error
-- -- --     cast (csource |wf| swf) (cdest |wf| dwf) reflp reflp x reflp reflp | h1  | h2  | Hβ§L xβ = pure (β§ cdest)
-- -- --     cast (csource |wf| swf) (cdest |wf| dwf) reflp reflp x reflp reflp | h1  | h2  | Hβ§R xβ = pure (β§ cdest)
-- -- --     cast (csource |wf| swf) (cdest |wf| dwf) reflp reflp x reflp reflp | .(HStatic _)  | .(HStatic _)  | HNeq xβ = pure (β§ cdest)
-- -- --     -- Converting from β to itself is the identity
-- -- --     cast (Cβ |wf| swf) (Cβ |wf| dwf) reflp reflp x reflp reflp | .Hβ  | Hβ  | HβL reflp xβ = pure x
-- -- --     cast (Cβ |wf| swf) (cdest |wf| dwf) reflp reflp x reflp reflp | .Hβ  | Hβ§  | HβL reflp xβ with () β xβ reflp
-- -- --     -- We convert to β by going through the germ
-- -- --     cast (csource |wf| swf) (Cβ |wf| dwf) reflp reflp x reflp reflp | .(HStatic _) |  Hβ | HβR xβ = do
-- -- --       xgerm β toGerm (csource |wf| swf) reflp reflp eq1 x reflp reflp
-- -- --       germToβ xgerm
-- -- --     -- Converting from β to a static-headed type, we go throug the germ, checking that the head matches
-- -- --     cast (Cβ |wf| swf) (cdest |wf| dwf) reflp reflp x reflp reflp | .Hβ  | HStatic h  | HβL reflp xβ with valueHead {β} Cβ reflp x in vheq
-- -- --     --Error at type β turns to error
-- -- --     cast (Cβ |wf| swf) (cdest |wf| dwf) reflp reflp x reflp reflp | .Hβ  | HStatic h  | HβL reflp xβ | VHβ§  = pure (β§ cdest)
-- -- --     -- β at type β turns to β at the destination type
-- -- --     cast (Cβ |wf| swf) (cdest |wf| dwf) reflp reflp x reflp reflp | .Hβ  | HStatic h  | HβL reflp xβ | VHββ  =
-- -- --       pure (oβ (self (<oQuadR reflp (<oPairL (β€o-sucMono (βsuc x))))) (cdest |wf| dwf) reflp reflp reflp reflp)
-- -- --     cast (Cβ |wf| swf) (cdest |wf| dwf) reflp reflp x reflp reflp | .Hβ  | HStatic h  | HβL reflp xβ | HVInβ hx _ with headDecEq h hx
-- -- --     -- If the heads don't match, the cast produces an error
-- -- --     cast (Cβ |wf| swf) (cdest |wf| dwf) reflp reflp x reflp reflp | .Hβ  | HStatic h  | HβL reflp xβ | HVInβ hx _  | no _ = pure (β§ cdest)
-- -- --     -- If the heads match, then we convert from β to the germ, then to the destination
-- -- --     cast (Cβ |wf| swf) (cdest |wf| dwf) reflp reflp x reflp reflp | .Hβ  | HStatic h  | HβL reflp xβ | HVInβ hx _  | yes reflp = do
-- -- --       let xg = germFromβ x vheq
-- -- --       fromGerm (cdest |wf| dwf) reflp reflp eq2 x reflp reflp
-- -- --     -- Otherwise, we have a conversion between types with the same head
-- -- --     cast (csource |wf| swf) (cdest |wf| dwf) reflp reflp x reflp reflp | .(HStatic _)  | .(HStatic _)  | HEq xβ = {!!}


-- -- -- -- castMeet : β β cs1 cs2 vs1 vs2 β SizedCastMeet β cs1 cs2 vs1 vs2
-- -- -- -- castMeet β.zero cs1 cs2 vs1 vs2 = oQuadRec (Ξ» (cs1 , cs2) (vs1 , vs2) β SizedCastMeet 0 cs1 cs2 vs1 vs2)
-- -- -- --   Ξ» (cs1 , cs2) (vs1 , vs2) self β castMeetRec 0 cs1 cs2 vs1 vs2 (self (_ , _) (_ , _)) Ξ» { {{()}} }
-- -- -- -- castMeet (β.suc β) cs1 cs2 vs1 vs2 = oQuadRec (Ξ» (cs1 , cs2) (vs1 , vs2) β SizedCastMeet (β.suc β) cs1 cs2 vs1 vs2)
-- -- -- --   Ξ» (cs1 , cs2) (vs1 , vs2) self β castMeetRec (β.suc β) cs1 cs2 vs1 vs2 (self (_ , _) (_ , _)) (castMeet β _ _ _ _)



-- -- -- -- -- -- -- castMeetRec : (size : Ord) β
-- -- -- -- -- -- --       (self ? -- : {y : Ord} β (y <o size) β CastMeet y) β CastMeet size
-- -- -- -- -- -- -- CastMeet.oCast (castMeetRec size self ? --) cβ cβ x with codeHead cβ in eq1 | codeHead cβ in eq2 | headMatchView (codeHead cβ) (codeHead cβ)
-- -- -- -- -- -- -- -- Casting from β§ is always error
-- -- -- -- -- -- -- ... | h1 |  h2 |  Hβ§L xβ = pure (β§ cβ )
-- -- -- -- -- -- -- -- Casting to β§ is always error
-- -- -- -- -- -- -- ... | h1 |  h2 |  Hβ§R xβ = pure (β§ cβ)
-- -- -- -- -- -- -- -- Casting between types with different heads is an error
-- -- -- -- -- -- -- ... | .(HStatic _) |  .(HStatic _) |  HNeq xβ = pure (β§ cβ)
-- -- -- -- -- -- -- ... | h1 |  Hβ§ |  HβL xβ xβ with () β xβ reflp
-- -- -- -- -- -- -- --Casting from a type to β
-- -- -- -- -- -- -- oCast (castMeetRec .(codeSize {β} cβ +o codeSize {β} Cβ) self ? --) {β} cβ Cβ {reflp} x | (HStatic h) |  .Hβ |  HβR reflp = do
-- -- -- -- -- -- --   xgerm β self ? -- {!!} .oToGerm cβ (ptoc eq1) x
-- -- -- -- -- -- --   pure (germToβ {h = h} xgerm)
-- -- -- -- -- -- -- -- Casting from β to a type
-- -- -- -- -- -- -- -- If the target type is β, we don't have to do anything
-- -- -- -- -- -- -- CastMeet.oCast (castMeetRec size self ? --) Cβ Cβ x | .Hβ |  Hβ |  HβL reflp xβ = pure x
-- -- -- -- -- -- -- -- If the destination type has a static head, we check what value we have from β
-- -- -- -- -- -- -- CastMeet.oCast (castMeetRec size self ? --) Cβ cβ x | .Hβ |  HStatic h2 |  HβL reflp xβ with valueHead Cβ reflp x in eq
-- -- -- -- -- -- -- -- If it is β, produce β at the target type
-- -- -- -- -- -- -- CastMeet.oCast (castMeetRec size self ? --) Cβ cβ {reflp} x | .Hβ |  HStatic h2 |  HβL reflp xβ | VHββ = pure (self ? -- (β€o-refl _) .oβ  cβ)
-- -- -- -- -- -- -- -- If it is β§, produce β§ at the target type
-- -- -- -- -- -- -- CastMeet.oCast (castMeetRec size self ? --) Cβ cβ x | .Hβ |  HStatic h2 |  HβL reflp xβ | VHβ§ = pure (β§ cβ)
-- -- -- -- -- -- -- -- Otherwise, we check if the value's head matches the target type
-- -- -- -- -- -- -- CastMeet.oCast (castMeetRec size self ? --) Cβ cβ {reflp} x | .Hβ |  HStatic h2 |  HβL reflp xβ | HVInβ h1 hrest with headDecEq h1 h2
-- -- -- -- -- -- --   -- If the value from β has the same head as the target code, then we cast through the germ
-- -- -- -- -- -- -- ... | yes reflp = do
-- -- -- -- -- -- --   xgerm β germFromβ x eq
-- -- -- -- -- -- --   self ? -- {!!} .oFromGerm cβ (ptoc eq2) xgerm
-- -- -- -- -- -- -- -- Otherwise, we produce an error
-- -- -- -- -- -- -- ... | no neq = pure (β§ cβ)
-- -- -- -- -- -- -- CastMeet.oCast (castMeetRec size self ? --) (CΞ  cβ cod) (CΞ  cβ codβ) x | HStatic HΞ  |  .(HStatic HΞ ) |  HEq reflp = {!!}
-- -- -- -- -- -- -- CastMeet.oCast (castMeetRec size self ? --) (CΞ£ cβ cod) (CΞ£ cβ codβ) x | HStatic HΞ£ |  .(HStatic HΞ£) |  HEq reflp = {!!}
-- -- -- -- -- -- -- CastMeet.oCast (castMeetRec size self ? --) (Cβ‘ cβ xβ y) (Cβ‘ cβ xβ yβ) x | HStatic Hβ |  .(HStatic Hβ) |  HEq reflp = do

-- -- -- -- -- -- --   pure {!!}
-- -- -- -- -- -- -- CastMeet.oCast (castMeetRec size self ? --) Cπ Cπ x | HStatic Hπ |  .(HStatic Hπ) |  HEq reflp = pure x
-- -- -- -- -- -- -- CastMeet.oCast (castMeetRec size self ? --) Cπ Cπ x | HStatic Hπ |  .(HStatic Hπ) |  HEq reflp = pure x
-- -- -- -- -- -- -- CastMeet.oCast (castMeetRec size self ? --) {suc β} CType CType x | HStatic HType |  .(HStatic HType) |  HEq reflp = pure x
-- -- -- -- -- -- -- CastMeet.oCast (castMeetRec size self ? --) (CΞΌ tyCtor cβ D xβ) (CΞΌ tyCtorβ cβ Dβ xβ) x | HStatic (HCtor xβ) |  .(HStatic (HCtor xβ)) |  HEq reflp = {!!}

-- -- -- -- -- -- -- CastMeet.oMeet (castMeetRec size self ? --) c x y {reflp} with codeHead c in eqc
-- -- -- -- -- -- -- ... | ch with valueHead c eqc x in eq1 | valueHead c eqc y in eq2 | valHeadMatchView (valueHead c eqc x) (valueHead c eqc y)
-- -- -- -- -- -- -- -- If either arg is β§ or the heads don't match, produce an error
-- -- -- -- -- -- -- ... |  h1 |  h2 |  VHβ§L xβ = pure (β§ c)
-- -- -- -- -- -- -- ... |  h1 |  h2 |  VHβ§R xβ = pure (β§ c)
-- -- -- -- -- -- -- ... |  .(HVal _) |  .(HVal _) |  VHNeq xβ = pure (β§ c)
-- -- -- -- -- -- -- ... |  .(HVInβ _ _) |  .(HVInβ _ _) |  VHNeqβ xβ = pure (β§ c)
-- -- -- -- -- -- -- -- If either arg is β, return the other argu
-- -- -- -- -- -- -- ... |  h1 |  h2 |  VHβL xβ xβ = pure y
-- -- -- -- -- -- -- ... |  .(HVal _) |  h2 |  VHβR xβ = pure x
-- -- -- -- -- -- -- ... |  h1 |  h2 |  VHInβL xβ xβ = pure y
-- -- -- -- -- -- -- ... |  .(HVInβ _ _) |  h2 |  VHInβR xβ = pure x
-- -- -- -- -- -- -- -- Meet when the head matches
-- -- -- -- -- -- -- -- Unit: nothing to do, just produce unit
-- -- -- -- -- -- -- oMeet (castMeetRec .(codeSize {β} Cπ) self ? --) {β} Cπ x y {reflp} | .(HStatic _) |  HVal h |  HVal h |  VHEq reflp
-- -- -- -- -- -- --   = pure true
-- -- -- -- -- -- -- -- Types: head must match, so just take the meet of the parts
-- -- -- -- -- -- -- oMeet (castMeetRec .(codeSize (CType )) self ? --) {suc β} CType  x y {reflp} | .(HStatic _) |  HVal h |  HVal h |  VHEq reflp
-- -- -- -- -- -- --   = {!!}
-- -- -- -- -- -- -- -- Functions: make the function that takes the meet of the result of the given functions
-- -- -- -- -- -- -- oMeet (castMeetRec .(codeSize (CΞ  dom cod)) self ? --) (CΞ  dom cod) f1 f2 {reflp} | .(HStatic _) |  HVal h |  HVal h |  VHEq reflp
-- -- -- -- -- -- --   = liftFunDep (Ξ» x β
-- -- -- -- -- -- --     self ? -- (β€o-sucMono (β€o-trans (β€o-cocone (Ξ» xβ β codeSize (cod xβ)) x (β€o-refl (codeSize (cod x)))) omax-β€R))
-- -- -- -- -- -- --       .oMeet (cod x) (f1 x) (f2 x))
-- -- -- -- -- -- -- oMeet (castMeetRec .(codeSize (CΞ£ dom cod)) self ? --) (CΞ£ dom cod) (x1 , x2) (y1 , y2) {reflp} | .(HStatic _) |  HVal h |  HVal h |  VHEq reflp
-- -- -- -- -- -- --   = do
-- -- -- -- -- -- --     xy1 β
-- -- -- -- -- -- --       self ? -- (β€o-sucMono (omax-β€L))
-- -- -- -- -- -- --         .oMeet dom x1 y1
-- -- -- -- -- -- --     x2cast β
-- -- -- -- -- -- --       self ? -- (β€o-sucMono (β€o-trans {!!} omax-β€R))
-- -- -- -- -- -- --         .oCast (cod x1) (cod xy1) x2
-- -- -- -- -- -- --     xy2 β
-- -- -- -- -- -- --       self ? -- {!!}
-- -- -- -- -- -- --         .oMeet (cod xy1) {!!} {!!}
-- -- -- -- -- -- --     pure {!!}
-- -- -- -- -- -- -- oMeet (castMeetRec .(codeSize (Cβ‘ c xβ yβ)) self ? --) (Cβ‘ c xβ yβ) x y {reflp} | .(HStatic _) |  HVal h |  HVal h |  VHEq reflp
-- -- -- -- -- -- --   = {!!}
-- -- -- -- -- -- -- oMeet (castMeetRec .(codeSize (CΞΌ tyCtor c D xβ)) self ? --) (CΞΌ tyCtor c D xβ) x y {reflp} | .(HStatic _) |  HVal h |  HVal h |  VHEq reflp
-- -- -- -- -- -- --   = {!!}
-- -- -- -- -- -- -- -- Meet for elements of β when the head matches
-- -- -- -- -- -- -- ... |  .(HVInβ _ _) |  .(HVInβ _ _) |  VHEqβ xβ = {!!}
-- -- -- -- -- -- -- -- oMeet (castMeetRec .(codeSize Cβ§) self ? --) Cβ§ x y {reflp} | h1 |  h2 |  v | Hβ§  = pure tt
-- -- -- -- -- -- -- CastMeet.oToGerm (castMeetRec size self ? --) = {!!}
-- -- -- -- -- -- -- CastMeet.oFromGerm (castMeetRec size self ? --) = {!!}
-- -- -- -- -- -- -- CastMeet.oβ (castMeetRec size self ? --) = {!!}

-- -- -- -- -- -- -- -- -- β : β {β} β (c--  : β β) β El c
-- -- -- -- -- -- -- -- -- cast : β {β} β (cβ cβ : β β) β El cβ -> (El cβ)
-- -- -- -- -- -- -- -- -- -- castDesc : β {β} (tyCtor1 tyCtor2 : CName)
-- -- -- -- -- -- -- -- -- --         β (c1 c2 : β β)
-- -- -- -- -- -- -- -- -- --         β (D1 : DName tyCtor1 β βDesc c1)
-- -- -- -- -- -- -- -- -- --         β (D2 : DName tyCtor2 β βDesc c2)
-- -- -- -- -- -- -- -- -- --         β (iβ : El c1) β (iβ : El c2)
-- -- -- -- -- -- -- -- -- --         β ΞΌ (Arg (DName tyCtor1) Ξ» d β interpDesc (D1 d)) iβ
-- -- -- -- -- -- -- -- -- --         β (ΞΌ (Arg (DName tyCtor2) Ξ» d β interpDesc (D2 d)) iβ)
-- -- -- -- -- -- -- -- -- toGerm : β {β} (c : β β) (h : Head) β codeHead c β‘p HStatic h β El c β germ h β
-- -- -- -- -- -- -- -- -- fromGerm : β {β} (c : β β) (h : Head) β codeHead c β‘p HStatic h β germ h β β El c
-- -- -- -- -- -- -- -- -- packGerm :   β {β} (h : Head) β germ h β β βTy β
-- -- -- -- -- -- -- -- -- unpackGerm :  β {β} (h : Head) β βTy β β germ h β
-- -- -- -- -- -- -- -- -- _β[_]_  : β {β} {c : β β} β El c β (c' : β β) β El c β {@(tactic default (reflp {A = β β} {c})) pf : c β‘p c'} β El c
-- -- -- -- -- -- -- -- -- codeMeet : β {β} (c1 c2 : β β) β β β


-- -- -- -- -- -- -- -- -- cast cβ cβ x with  codeHead cβ in eq1 | codeHead cβ in eq2 | headMatchView (codeHead cβ) (codeHead cβ)
-- -- -- -- -- -- -- -- -- ... | h1 | h2 | Hβ§L xβ =  (β§ cβ)
-- -- -- -- -- -- -- -- -- ... | h1 | h2 | Hβ§R xβ = (β§ cβ)
-- -- -- -- -- -- -- -- -- cast Cβ Cβ x | Hβ |  Hβ  | HβL xβ xβ = x
-- -- -- -- -- -- -- -- -- cast cβ Cβ§ x | Hβ |  Hβ§ |  HβL xβ xβ = tt
-- -- -- -- -- -- -- -- -- ... | .(HStatic _) | .(HStatic _) | HNeq xβ = (β§ cβ)
-- -- -- -- -- -- -- -- -- cast (CΞ  dom1 cod1) (CΞ  dom2 cod2) f | .(HStatic HΞ ) |  .(HStatic HΞ ) |  HEq {h1 = HΞ } reflp
-- -- -- -- -- -- -- -- --   = {!!}
-- -- -- -- -- -- -- -- --   -- ret
-- -- -- -- -- -- -- -- --   --  where
-- -- -- -- -- -- -- -- --   --    ret : El (CΞ  dom2 cod2)
-- -- -- -- -- -- -- -- --   --    ret x2 = do
-- -- -- -- -- -- -- -- --   --      let x1 = cast dom2 dom1 x2
-- -- -- -- -- -- -- -- --   --      fx1 β f x1
-- -- -- -- -- -- -- -- --   --      pure (cast (cod1 x1) (cod2 x2) fx1)
-- -- -- -- -- -- -- -- -- cast (CΞ£ dom1 cod1) (CΞ£ dom2 cod2) (x1 , y1) | .(HStatic HΞ£) |  .(HStatic HΞ£) |  HEq {h1 = HΞ£} reflp
-- -- -- -- -- -- -- -- --   = let x2 = cast dom1 dom2 x1
-- -- -- -- -- -- -- -- --     in (x2 , cast (cod1 x1) (cod2 x2) y1)
-- -- -- -- -- -- -- -- -- cast (Cβ‘ cβ xβ y) (Cβ‘ cβ xβ yβ) (wit β’ _ β _) | .(HStatic Hβ) |  .(HStatic Hβ) |  HEq {h1 = Hβ} reflp
-- -- -- -- -- -- -- -- --   = cast cβ cβ wit β’ xβ β yβ
-- -- -- -- -- -- -- -- -- cast Cπ Cπ x | .(HStatic Hβ€) |  .(HStatic Hβ€) |  HEq {h1 = Hβ€} reflp
-- -- -- -- -- -- -- -- --   = x
-- -- -- -- -- -- -- -- -- cast Cπ Cπ x | .(HStatic Hβ₯) |  .(HStatic Hβ₯) |  HEq {h1 = Hβ₯} reflp
-- -- -- -- -- -- -- -- --   = x
-- -- -- -- -- -- -- -- -- cast CType CType x | .(HStatic HType) |  .(HStatic HType) |  HEq {h1 = HType} reflp
-- -- -- -- -- -- -- -- --   = x
-- -- -- -- -- -- -- -- -- cast (CΞΌ tyCtor1 cβ D xβ) (CΞΌ tyCtor2 cβ Dβ xβ) x | .(HStatic (HCtor xβ)) |  .(HStatic (HCtor xβ)) |  HEq {h1 = HCtor xβ} reflp
-- -- -- -- -- -- -- -- --   = {!!} --castDesc tyCtor1 tyCtor2 cβ cβ D Dβ xβ xβ x
-- -- -- -- -- -- -- -- -- cast Cβ cβ x | Hβ | HStatic h | HβL xβ xβ
-- -- -- -- -- -- -- -- --   = fromGerm cβ h eq2 (unpackGerm h x)
-- -- -- -- -- -- -- -- -- cast cβ Cβ x | (HStatic h) |  Hβ |  HβR xβ
-- -- -- -- -- -- -- -- --   = packGerm h (toGerm cβ h eq1 x)



-- -- -- -- -- -- -- -- -- β Cβ = ββ
-- -- -- -- -- -- -- -- -- β Cβ§ = tt
-- -- -- -- -- -- -- -- -- β Cπ = tt
-- -- -- -- -- -- -- -- -- β Cπ = true
-- -- -- -- -- -- -- -- -- β {suc β} CType = Cβ
-- -- -- -- -- -- -- -- -- β (CΞ  dom cod) = Ξ» x β {!!} --pure (β (cod x))
-- -- -- -- -- -- -- -- -- β (CΞ£ dom cod) = β dom , β (cod (β dom))
-- -- -- -- -- -- -- -- -- β (Cβ‘ c x y) = (x β[ c ] y) β’ x β y
-- -- -- -- -- -- -- -- -- β (CΞΌ tyCtor c D x) = {!!} --ΞΌβ

-- -- -- -- -- -- -- -- -- _β[_]_ x c y {reflp} with valueHead {c = c} x in eq1 | valueHead {c = c} y in eq2 |  headMatchView  (valueHead {c = c} x) (valueHead {c = c} y)
-- -- -- -- -- -- -- -- -- ... | h1 | h2 | Hβ§L xβ = β§ c
-- -- -- -- -- -- -- -- -- ... | h1 | h2 | Hβ§R xβ = β§ c
-- -- -- -- -- -- -- -- -- ... | Hβ |  h2 |  HβL xβ xβ = y
-- -- -- -- -- -- -- -- -- ... | .(HStatic _) | Hβ | HβR xβ = x
-- -- -- -- -- -- -- -- -- ... | .(HStatic _) | .(HStatic _) | HNeq xβ = β§ c
-- -- -- -- -- -- -- -- -- (x β[ Cπ ] y) {reflp} | .(HStatic _) | .(HStatic _) | HEq xβ = x and y
-- -- -- -- -- -- -- -- -- (f β[ CΞ  dom cod ] g) {reflp} | .(HStatic _) | .(HStatic _) | HEq xβ = Ξ» x β {!!} -- β¦ _β[ cod x ]_ (f x)  (g x) β¦
-- -- -- -- -- -- -- -- -- ((x1 , y1) β[ CΞ£ dom cod ] (x2 , y2)) {reflp} | .(HStatic _) | .(HStatic _) | HEq xβ = (x1 β[ dom ] x2) , (cast (cod x1) (cod _) y1 β[ cod _ ] cast (cod x2) (cod _) y2)
-- -- -- -- -- -- -- -- -- ((w1 β’ x β y) β[ Cβ‘ c x y ] (w2 β’ x β y)) {reflp} | .(HStatic _) | .(HStatic _) | HEq xβ = (w1 β[ c ] w2) β’ x β y
-- -- -- -- -- -- -- -- -- (x β[ CΞΌ tyCtor c D xβ ] y) {reflp} | .(HStatic _) | .(HStatic _) | HEq xβ = {!!}
-- -- -- -- -- -- -- -- -- _β[_]_ {suc β} x CType y {reflp} | .(HStatic _) | .(HStatic _) | HEq xβ = codeMeet x y


-- -- -- -- -- -- -- -- -- -- Meet of elements at type β
-- -- -- -- -- -- -- -- -- (βΞ  f β[ Cβ ] βΞ  g) {reflp} | HStatic HΞ  | .(HStatic HΞ ) | HEq reflp
-- -- -- -- -- -- -- -- --   = βΞ  (Ξ» x β β¦ _β[ Cβ ]_ (f x) (g x) β¦)
-- -- -- -- -- -- -- -- -- (βΞ£ (x1 , y1) β[ Cβ ] βΞ£ (x2 , y2)) {reflp} | HStatic HΞ£ | .(HStatic HΞ£) | HEq reflp
-- -- -- -- -- -- -- -- --   = βΞ£ ((x1 β[ Cβ ] x2) , (y1 β[ Cβ ] y2))
-- -- -- -- -- -- -- -- -- (ββ‘ (x β’ _ β _) β[ Cβ ] ββ‘ (y β’ _ β _)) {reflp} | HStatic Hβ | .(HStatic Hβ) | HEq reflp = ββ‘ ((x β[ Cβ ] y) β’ _ β _)
-- -- -- -- -- -- -- -- -- (βπ β[ Cβ ] βπ) {reflp} | HStatic Hβ€ | .(HStatic Hβ€) | HEq reflp = βπ
-- -- -- -- -- -- -- -- -- _β[_]_ {suc β} (βType x) Cβ (βType y) {reflp} | HStatic HType |  .(HStatic HType) | HEq reflp = βType {{inst = suc<}} (codeMeet x y)
-- -- -- -- -- -- -- -- -- (βΞΌ tyCtor ctor x β[ Cβ ] βΞΌ tyCtorβ ctorβ xβ) {reflp} | HStatic (HData tyCtorβ xβ) | .(HStatic (HData tyCtorβ xβ)) | HEq reflp = {!!}

-- -- -- -- -- -- -- -- -- codeMeet c1 c2 with codeHead c1 in eq1 | codeHead c2 in eq2 | headMatchView (codeHead c1) (codeHead c2)
-- -- -- -- -- -- -- -- -- ... | h1 | h2 | Hβ§L x = Cβ§
-- -- -- -- -- -- -- -- -- ... | h1 | h2 | Hβ§R x = Cβ§
-- -- -- -- -- -- -- -- -- ... | h1 | h2 | HβL x xβ = c2
-- -- -- -- -- -- -- -- -- ... | .(HStatic _) | h2 | HβR x = c1
-- -- -- -- -- -- -- -- -- ... | .(HStatic _) | .(HStatic _) | HNeq x = Cβ§
-- -- -- -- -- -- -- -- -- codeMeet (CΞ  dom1 cod1) (CΞ  dom2 cod2) | HStatic HΞ  | .(HStatic HΞ ) | HEq reflp
-- -- -- -- -- -- -- -- --   = CΞ  (codeMeet dom1 dom2) Ξ» x β codeMeet (cod1 (cast (codeMeet dom1 dom2) dom1 x)) (cod2 (cast (codeMeet dom1 dom2) dom2 x))
-- -- -- -- -- -- -- -- -- codeMeet (CΞ£ dom1 cod1) (CΞ£ dom2 cod2) | HStatic HΞ£ | .(HStatic HΞ£) | HEq reflp
-- -- -- -- -- -- -- -- --   = CΞ  (codeMeet dom1 dom2) Ξ» x β codeMeet (cod1 (cast (codeMeet dom1 dom2) dom1 x)) (cod2 (cast (codeMeet dom1 dom2) dom2 x))
-- -- -- -- -- -- -- -- -- codeMeet (Cβ‘ c1 x1 y1) (Cβ‘ c2 x2 y2) | HStatic Hβ | .(HStatic Hβ) | HEq reflp
-- -- -- -- -- -- -- -- --   = Cβ‘ c12 (cast c1 c12 x1 β[ c12 ] cast c2 c12 x2) (cast c1 c12 y1 β[ c12 ] cast c2 c12 y2)
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --       c12 = codeMeet c1 c2
-- -- -- -- -- -- -- -- -- codeMeet Cπ Cπ | HStatic Hβ€ | .(HStatic Hβ€) | HEq reflp = Cπ
-- -- -- -- -- -- -- -- -- codeMeet Cπ Cπ | HStatic Hβ₯ | .(HStatic Hβ₯) | HEq reflp = Cπ
-- -- -- -- -- -- -- -- -- codeMeet (CType {{inst = inst}}) CType | HStatic HType | .(HStatic HType) | HEq reflp = CType {{inst = inst}}
-- -- -- -- -- -- -- -- -- codeMeet (CΞΌ tyCtor c1 D x) (CΞΌ tyCtorβ c2 Dβ xβ) | HStatic (HCtor xβ) | .(HStatic (HCtor xβ)) | HEq reflp = {!!}

-- -- -- -- -- -- -- -- -- toGerm (CΞ  dom cod) HΞ  p f = Ξ» x β {!!} -- β¦ (cast (cod (cast Cβ dom x)) Cβ) (f (cast Cβ dom x)) β¦
-- -- -- -- -- -- -- -- -- toGerm (CΞ£ dom cod) HΞ£ p (x , y) = cast dom Cβ x , cast (cod x) Cβ y
-- -- -- -- -- -- -- -- -- toGerm (Cβ‘ c xβ y) Hβ p (wit β’ _ β _) = cast c Cβ wit β’ _ β _
-- -- -- -- -- -- -- -- -- toGerm Cπ Hβ€ p x = x
-- -- -- -- -- -- -- -- -- toGerm Cπ Hβ₯ p x = x
-- -- -- -- -- -- -- -- -- toGerm {suc β} CType HType p x = x
-- -- -- -- -- -- -- -- -- toGerm (CΞΌ tyCtor c D xβ) (HCtor xβ) p x = {!!}

-- -- -- -- -- -- -- -- -- fromGerm c h p x = {!!}
