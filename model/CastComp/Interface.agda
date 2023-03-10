
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Sum
import Cubical.Data.Empty as Empty
-- open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
-- open import Cubical.Data.Equality
open import UnkGerm
open import GuardedAlgebra
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude

open import ApproxExact
open import InductiveCodes
open import Sizes
-- open import CodePair

module CastComp.Interface {{_ : DataTypes}} {{_ : DataGerms}} {{_ : CodesForInductives}}   where

open import Code
open import Head
open import Util
-- open Ord â El â§ Cð refl
open import Cubical.Data.FinData.Properties as Fin
import Cubical.Data.Nat.Order as Nat

import GuardedModality as â¹Mod
open import Cubical.Data.Sum

open import Assumption



-- The tuple of things that are decreasing in our recursive calls
-- (A) Bool: flag for whether we're allowed to see â as a type
--  this is there for strict positivity: we get an extra recursive call when computing meet or cast of terms in the germ of an inductive type
--  because we're guaranteed that, within an inductive type, we never see unguarded â to the left of an arrow (because of strict positivity).
--  This lets us do induction on the size of the value for everything but functions, where we know we're not seeing â
-- (B) â: the universe level we're currently in. We need this so that, when (c  = CType) and (v1 v2 : El c), for the meet of v1 and v2, we can call codeMeet
--    at the smalelr universe, letting us move the size of the value into the code value
-- (C) Code size: the size of the code, either being combined with code meet, or the code of the values being cast/composed
-- (D) Value size: the size of the value currently being operated on. Set to S0 for codeMeet.
CastCompMeasure : Set
CastCompMeasure = â Ã Size Ã Size

-- We can define the lexicographic-ordering on this measure
_<CastComp_ : (m1 m2 : CastCompMeasure) â Set
_<CastComp_ = _<Lex_ {_<a_ = Nat._<_} {_<b_ = _<Lex_ {_<a_ = _<â_}  {_<b_ = _<â_}}

CastCompWellFounded : WellFounded (Î» x y â â¥ x <CastComp y â¥â)
CastCompWellFounded = â¥LexWellFoundedâ¥ Nat.<-wellfounded (LexWellFounded sizeWF sizeWF)

open import Germ
record SizedCastMeet (â : â) (csize vsize : Size) : Set where
  field

    oâ : â {{Ã¦ : Ã}}
      â (c : â â)
      â (pfc1 : codeSize c â¡p csize )
      â (El c)

    oMeet : â {{Ã¦ : Ã}}
      â (c : â â)
      â (x y : El c)
      â ( pfc : (codeSize c)  â¡p csize)
      â LÃ (El c)

    -- oDataGermMeet : â {{Ã¦ : Ã}} {tyCtor}
    --   â (x y : âGermTy â tyCtor)
    --   â smax (GermSize x) (GermSize y) â¡p size
    --   â LÃ (âGermTy â tyCtor)


    oCodeMeet :
      (c1 c2 : â â)
      â ( pfc1 : smax (codeSize c1) (codeSize c2)  â¡p csize )
      â (â â)

    oCodeMeetSize :
      (c1 c2 : â â)
      â ( pfc1 : smax (codeSize c1) (codeSize c2)  â¡p csize )
      â codeSize (oCodeMeet c1 c2 pfc1) â¤â smax (codeSize c1) (codeSize c2)

    oCast : â {{Ã¦ : Ã}}
      â (csource cdest : â â)
      â  (x : El csource)
      â ( pfc1 : (smax (codeSize csource) (codeSize cdest)  â¡p csize))
      -> LÃ ( Î£[ xdest â El cdest ]( elSize cdest xdest â¤â elSize csource x ) )


open SizedCastMeet public

data Hide (a : Set) : Set where
  hide : â {arg : a} â Hide a

reveal : â {a} â Hide a â a
reveal (hide {arg = x}) = x


Decreasing_ : â {a : Set} â a â Hide a
Decreasing_ x = hide {arg = x}

infixr 99 Decreasing_

--If cSize is a codeSize, then cSize is not zero and we must not be in âpos mode
-- codeNotZero : â {â} {c : â â} {âAllowed} {A : Set}
--   â {@(tactic assumption) posNoCode : âAllowed â¡p âpos â SZ â¡p codeSize c}
--   â Hide (âAllowed â¡p âpos â A)
-- codeNotZero {c = c} {posNoCode = posNoCode} = hide {arg = Î» pf â Empty.elim (Â¬Z<â SZ (codeSuc c â¤â¨ pSubst (Î» x â x â¤â SZ) (posNoCode pf) â¤â-refl))}

-- maxNotZero : â {â} {c1 c2 : â â} {âAllowed} {A : Set}
--   â {@(tactic assumption) posNoCode : âAllowed â¡p âpos â SZ â¡p smax (codeSize c1) (codeSize c2)}
--   â Hide (âAllowed â¡p âpos â A)
-- maxNotZero {c1 = c1} {c2 = c2} {posNoCode = posNoCode} = hide {arg = Î» pf â Empty.elim (Â¬Z<â SZ (codeSuc c1 â¤â¨ smax-â¤L â¤â¨ pSubst (Î» x â x â¤â SZ) (posNoCode pf) â¤â-refl ))}


record SmallerCastMeet (â : â) (csize vsize : Size) : Set where
  constructor smallerCastMeet
  field
    self : â {â' cs vs} â â¥ ( â' , cs , vs) <CastComp ( â , csize , vsize) â¥â â SizedCastMeet â' cs vs
    â¹self : â {â' cs vs} â â¹Mod.â¹ (SizedCastMeet â' cs vs)
  --useful helper
  <cSize : â {cs} â (cs <â csize) â â¥ ( â , cs , SZ ) <CastComp ( â , csize , vsize) â¥â
  <cSize lt = â£ <LexR reflc (<LexL lt) â£â
  <vSize : â {vs} â (vs <â vsize) â â¥ ( â , csize , vs ) <CastComp ( â , csize , vsize) â¥â
  <vSize lt = â£ <LexR reflc (<LexR reflc lt) â£â

  infix 20 â_By_
  â_By_ : â {{_ : Ã}}
      â (c : â â) â (lt : Hide (codeSize c <â csize)) â (El c)
  â_By_  c (hide {lt}) = oâ (self (<cSize lt)) c reflp

  infix 20 [_]â_By_
  [_]â_By_ : â (Ã¦ : Ã)
      â (c : â â) â (lt : Hide (codeSize c <â csize)) â (El {{Ã¦ = Ã¦}} c)
  [_]â_By_ Ã¦  = â_By_ {{Ã¦}}

  infix 20 _â_â_By_
  _â_â_By_ : â {{_ : Ã}}
      â (c : â â)
      â (x y : El c)
      â (Hide (codeSize c <â csize))
      â LÃ (El c)
  _â_â_By_  c x y (hide {ltc}) = oMeet (self (<cSize ltc)) c x y reflp
  -- with âmatch âAllowed
  -- ... | inl reflp = oMeet (self (<Size ltc)) c x y reflp
  -- ... | inr (inl reflp) = oMeet (self (<Size ltc)) c x y  reflp
  -- ... | inr (inr reflp) = oMeet (self (<Size ltc)) c x y reflp
  --     -- oMeet (self  (<Size lt)) c x y reflp

  infix 20 [_]_â_â_By_
  [_]_â_â_By_ : â (Ã¦ : Ã)
      â (c : â â)
      â (x y : El {{Ã¦ = Ã¦}} c)
      â  (Hide( codeSize c <â csize))
      â LÃ {{Ã¦ = Ã¦}} (El {{Ã¦ = Ã¦}} c)
  [_]_â_â_By_ Ã¦ = _â_â_By_ {{Ã¦}}


  infix 20 _â_By_
  _â_By_ :
      (c1 c2 : â â)
      â (lt : Hide (smax (codeSize c1) (codeSize c2) <â csize))
      â (â â)
  _â_By_  c1 c2 (hide {lt}) =
      oCodeMeet (self (<cSize lt)) c1 c2 reflp

  -- infix 20 _ââ_By_
  -- _ââ_By_ :
  --     {{_ : Ã}}
  --     (x1 x2 : âTy â)
  --     â (cpf : S1 â¡p cSize)
  --     â (lt : Hide (smax (elSize Câ x1) (elSize Câ x2 ) <â vSize))
  --     â LÃ (âTy â)
  -- _ââ_By_  x1 x2 cpf (hide {lt}) = oMeet (self (<VSize (ptoc cpf) lt)) Câ x1 x2 {!!} reflp

  codeMeetEq : â
      (c1 c2 : â â)
      â {lt1 lt2 : Hide (smax (codeSize c1) (codeSize c2) <â csize)}
      â ApproxEl (c1 â c2 By lt1) â¡ ApproxEl (c1 â c2 By lt2)
  codeMeetEq  c1 c2 {hide {arg = lt1}} {hide {arg = lt2}} = (cong (Î» lt â ApproxEl (oCodeMeet (self lt) c1 c2 reflp))) (squashâ (<cSize lt1) (<cSize lt2))

  infix 20 _âSize_By_
  _âSize_By_ :
      (c1 c2 : â â)
      â (lt : Hide (smax (codeSize c1) (codeSize c2) <â csize))
      â  codeSize (c1 â c2 By lt ) â¤â smax (codeSize c1) (codeSize c2)
  _âSize_By_ c1 c2 (hide {lt}) =
      oCodeMeetSize (self (<cSize lt)) c1 c2 reflp

  infix 20 â¨_â_â©_By_
  â¨_â_â©_By_ : â {{_ : Ã}}
      â (cdest csource : â â)
      â (x : El csource)
       â (Hide (smax (codeSize csource)  (codeSize cdest) <â csize))
      â LÃ (El cdest)
  â¨_â_â©_By_ cdest csource x (hide {clt})
    = fst <$> oCast (self (<cSize clt)) csource cdest x reflp


  infix 20 [_]â¨_â_â©_By_
  [_]â¨_â_â©_By_ : â (Ã¦ : Ã)
      â (cdest csource : â â)
      â (x : El {{Ã¦ = Ã¦}} csource)
      â     Hide  (smax (codeSize csource)  (codeSize cdest) <â csize)
      â LÃ {{Ã¦ = Ã¦}} (El {{Ã¦ = Ã¦}} cdest)
  [_]â¨_â_â©_By_ Ã¦ = â¨_â_â©_By_ {{Ã¦}}


  -- Helper to manage the common case of having two elements of different codes' types,
  -- casting them to the meet code, then taking the meet of those two elements
  infix 20 _,,_â_â_By_
  _,,_â_â_By_ :
    â {{Ã¦ : Ã}} â
    â c1 c2 â
      (x : El c1) â
      (y : El c2) â
      (clt : Hide (smax (codeSize c1) (codeSize c2) <â csize)) â
      -- (vlt : Hide (âAllowed â¡p âpos â smax (elSize c1 x) (elSize c2 y) <â vSize)) â
      {lt : _} â
      LÃ (El (c1 â c2 By (hide {arg = lt }) ))
  _,,_â_â_By_  c1 c2 x1 x2 clt  {lt = lt} = do
   -- let lt = smax<-â (reveal ltâ)
   let c12 = (c1 â c2 By hide {arg = lt})
   let
     lt1 =
       â¤â-sucMono
         (smax-monoR (c1 âSize c2 By hide {arg = lt})
         â¤â¨ smax-assocL (codeSize c1) (codeSize c1) (codeSize c2)
         â¤â¨ smax-monoL smax-idem
         )
         â¤â¨ reveal clt
   let
     lt2 =
       â¤â-sucMono (
         smax-monoR (c1 âSize c2 By hide {arg = lt} â¤â¨ smax-commut _ _)
         â¤â¨ smax-assocL _ _ _
         â¤â¨ smax-commut _ _
         â¤â¨ smax-monoR smax-idem
         )
       â¤â¨ reveal clt
   let
     lt12 =
       â¤â-sucMono (
         (c1 âSize c2 By hide {arg = lt})
         -- â¤â¨ smax-mono (smaxâ-self _) (smaxâ-self _)
         )
       â¤â¨ reveal clt
   x1-12 â  (â¨ c12 â c1 â© x1
        By
          Decreasing lt1
          -- hide {arg = Î» pf â â¤< smax-â¤L (reveal vlt pf) }
          )
   x2-12 â  (â¨ c12 â c2 â© x2
     By Decreasing lt2
     )
   c12 â x1-12 â x2-12
     By Decreasing lt12


  [_]_,,_â_â_By_ :
    â (Ã¦ : Ã)
      c1 c2 â
      (x : El {{Ã¦ = Ã¦}} c1) â
      (y : El {{Ã¦ = Ã¦}} c2) â
      (clt : Hide (smax ( codeSize c1) ( codeSize c2) <â csize)) â
      {lt : _} â
      LÃ {{Ã¦ = Ã¦}} (El {{Ã¦ = Ã¦}} (c1 â c2 By (hide {arg = lt }) ))
  [_]_,,_â_â_By_ Ã¦ = _,,_â_â_By_ {{Ã¦ = Ã¦}}



  â¨_,_âââ©_By_ : â {{Ã¦ : Ã}} c1 c2
      {lt : _}
    â let c1âc2 = (c1 â c2 By (hide {arg = lt }) )
    in (x12 : El c1âc2)
    â (clt : Hide ( smax (codeSize c1)  (codeSize c2) <â csize))
    â LÃ (El c1 Ã El c2)
  â¨_,_âââ©_By_ c1 c2  {lt = lt} x clt  = do
    let c12 = c1 â c2 By hide {arg = lt}
    let
      lt1 =
        â¤â-sucMono (
          smax-monoL (c1 âSize c2 By hide )
          â¤â¨ smax-commut _ _
          â¤â¨ smax-assocL _ _ _
          â¤â¨ smax-monoL smax-idem
          )
        â¤â¨ reveal clt
    let
      lt2 =
        â¤â-sucMono (
          smax-monoL (c1 âSize c2 By hide )
          â¤â¨ smax-assocR _ _ _
          â¤â¨ smax-monoR smax-idem)
        â¤â¨ reveal clt
    x1 â â¨ c1 â c12 â© x
      By Decreasing lt1
    x2 â  â¨ c2 â c12 â© x
      By Decreasing lt2
    pure (x1 , x2)

  [_]â¨_,_âââ©_By_ : â (Ã¦ : Ã) c1 c2
    â {lt : _}
    â let c1âc2 = (c1 â c2 By (hide {arg = lt }) )
    in (x12 : El {{Ã¦ = Ã¦}} c1âc2)
    â (clt : Hide (smax (codeSize c1)  (codeSize c2) <â csize))
    â LÃ {{Ã¦ = Ã¦}} (El {{Ã¦ = Ã¦}} c1 Ã El {{Ã¦ = Ã¦}} c2)
  [_]â¨_,_âââ©_By_ Ã¦ =  â¨_,_âââ©_By_ {{Ã¦ = Ã¦}}

  infix 20 â¨_â_â©â_By_
  â¨_â_â©â_By_ : â {{_ : Ã}}
      â (cdest csource : â â)
      â (x : El csource)
      â  Hide (smax (codeSize csource)  (codeSize cdest) <â csize)
      â LÃ ( Î£[ xdest â El cdest ]( elSize cdest xdest â¤â elSize csource x ) )
  â¨_â_â©â_By_ cdest csource x (hide {clt}) = oCast (self (<cSize clt)) csource cdest x reflp

  self-1 : â {cs vs} {{ inst : 0< â }} â SizedCastMeet (predâ â) cs vs
  self-1 â¦ suc< â¦ = self â£ <LexL Nat.â¤-refl â£â
  Lself :  â  {Ã¦ â' cs vs} â (Ã¦ â¡p Exact) â LÃ {{Ã¦ = Ã¦}} (SizedCastMeet â' cs vs)
  Lself reflp = Later {{Exact}} Î» tic â pure â¦ Exact â¦ (â¹self  tic)

FixCastMeet :
  (â { â  csize vsize} â SmallerCastMeet â csize vsize â SizedCastMeet â csize vsize)
  â â â csize vsize â SizedCastMeet â csize vsize
FixCastMeet f  =
  â¹Mod.fix Î» â¹self â
    Î» _ _ _ â
    WFI.induction CastCompWellFounded {P = Î» {(â' , cs , vs) â SizedCastMeet â' cs vs}}
      (Î» {(â' , cs , vs) â Î» self â f (smallerCastMeet (self ( _ , _ , _)) Î» {â'} {cs} {vs} â Î» tic â â¹self tic â' cs vs)}) _
