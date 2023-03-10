{-# OPTIONS --cubical --guarded --prop #-}


module Util where

open import Cubical.Data.Maybe
open import Cubical.Relation.Nullary
open import DecPEq
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Bool renaming (Bool to π)
open import Cubical.Data.FinData hiding (elim)
-- open import Cubical.Data.Prod
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Data.Empty

open import Agda.Builtin.Reflection
open import Agda.Primitive public

andBoth : β (b1 b2 : π) β (b1 and b2) β‘ true β (b1 β‘p true) Γ (b2 β‘p true)
andBoth false false pf with () β trueβ’false (sym pf)
andBoth false true pf with () β trueβ’false (sym pf)
andBoth true false pf with () β trueβ’false (sym pf)
andBoth true true pf = reflp , reflp


default : {A : Set} β A β Term β TC Unit
default x hole = bindTC (quoteTC x) (unify hole)


_β+_ : β β Level β Level
zero  β+ β = β
suc n β+ β = lsuc (n β+ β)

#_ : β β Level
#_ = _β+ lzero


data #_-1β‘_ : β -> Level -> Set where
  instance is-lsuc : β {β} -> #(suc β) -1β‘ # β

Set-1 : (β : β ) -> Set (# β)
Set-1 zero  = Unit*
Set-1 (suc β) = Set (# β)


ToSort : β {β} -> Set-1 β -> Set (# β)
ToSort {suc β} s = Lift s
ToSort {zero} s = β₯

typeof : β {β} {A : Set β} β A β Set β
typeof {A = A} _ = A


pathij : β {β} {A : Set β} {x y : A} β (pf : x β‘c y) β β i j β pf i β‘c pf j
pathij pf i j k = pf (( k β§ j) β¨ (~ k β§ i))


pathi0 : β {β} {A : Set β} {x y : A} β (pf : x β‘c y) β β i β pf i β‘c pf i0
pathi0 pf i = pathij pf i i0

pathi1 : β {β} {A : Set β} {x y : A} β (pf : x β‘c y) β β i β pf i β‘c pf i1
pathi1 pf i = pathij pf i i1

compPathEq : β {β} {A : I β Set β} {x : A i0} {y : A i1} {z : A i1} β PathP A x y β y β‘c z β PathP A x z
compPathEq pth peq = substPath (Ξ» w β PathP _ _ w) peq pth

compEqPath : β {β} {A : I β Set β} {x : A i0} {y : A i0} {z : A i1} β x β‘c y β PathP A y z β PathP A x z
compEqPath peq pth = substPath (Ξ» w β PathP _ w _) (sym peq) pth

reflCompose : β {β} {A : Set β} {x : A} β (refl {x = x} ) β‘c refl β refl
reflCompose {x = x}  = compPath-filler reflc Ξ» i β x

transportCompose : β {β} {A B C : Set β} β (pf1 : A β‘ B) β (pf2 : B β‘ C) β (a : A) β transport pf2 (transport pf1 a) β‘c transport (pf1 β pf2) a
transportCompose pf1 pf2 a
  =
  JPath (Ξ» y pf2 β transport pf2 (transport pf1 a) β‘c transport (pf1 β pf2) a)
  (JPath
    (Ξ» x pf1 β
      transportPath reflc (transportPath pf1 a) β‘c
      transportPath (compPath pf1 reflc) a)
    (transportRefl (transportPath reflc a) β transportRefl a β sym (transportRefl a) β congPath (Ξ» pf β transportPath pf a) reflCompose) pf1) pf2

path01eq : β {β} {A0 A1 : Set β} (Aeq : A0 β‘c A1) β β i β PathP (Ξ» j β Aeq i β‘ Aeq j) (pathi0 Aeq i)  (pathi1 Aeq i)
path01eq Aeq i j = pathij Aeq i j

path01Transport : β {β} {A0 A1 : Set β} (Aeq : A0 β‘c A1) β β i (a :  Aeq i) β PathP (Ξ» i β Aeq i) (transport (pathi0 Aeq i) a  ) (transport (pathi1 Aeq i) a)
path01Transport Aeq i a j = transportPath (pathij Aeq i j) a

-- funDomTrans : β A0 A1 (Aeq : A0 β‘c A1) (B : β {i} β  Aeq i β Set) β ((a : Aeq i0) β B {i0} a) β‘c

-- extP : β {A0 A1 : Set} (Aeq : A0 β‘c A1) {B : β {i} β  Aeq i β Set} β (f : (a : Aeq i0) β B {i0} a ) (g : (a : Aeq i1) β B {i1} a)
--   β (β {a0 : A0} {a1 : A1} (eqq : PathP (Ξ» i β Aeq i) a0 a1) β PathP (Ξ» i β B {i} (eqq i)) (f (eqq i0)) (g (eqq i1)))
--   β PathP (Ξ» i β (a : Aeq i) β B {i} a ) f g
-- extP Aeq {B = B} f g pf = {!!}
--   where
    -- pth : PathP (Ξ» j β B {i = j} (transport (pathij Aeq i j) a)) (f (transportPath (pathij Aeq i i0) a)) (g (transportPath (pathij Aeq i i1) a))
    -- pth = pf (path01Transport (Ξ» iβ β Aeq iβ) i a)

compPathPEx : β {β} (A : I β Set β) (x : A i0) (y : A i1) (B_i1 : Set β) (B : (A i1) β‘ B_i1) {z : B i1}
            β PathP A x y β PathP (Ξ» i β B i) y z β PathP (Ξ» j β ((Ξ» i β A i) β B) j) x z
compPathPEx A x y B_i1 B p q i =
  comp (Ξ» j β compPath-filler (Ξ» i β A i) B j i)
       (Ξ» j β Ξ» { (i = i0) β x ;
                  (i = i1) β q j })
       (p i)


transpFunLemma : β {β β'} {A : Set β} (P : A β Set β') (f : (a : A) β P a ) {x y} (pf : x β‘c y)
  β transport (cong P pf) (f x) β‘c (f y)
transpFunLemma P f {y = y} pf =
  (JPath {x = y} (Ξ» z zpf β transport (cong P (sym zpf)) (f z) β‘c transport refl (f y)) refl (sym pf)) β transportRefl (f _)



subLemma : β {β β'} {A : Set β} (P : A β Set β') (f : (a : A) β P a ) {x y} (pf : x β‘c y)
  β subst P pf (f x) β‘c (f  y)
subLemma P f pf = transpFunLemma P f pf

funExtI : β {β} {f g : I β Set β}
  β (β i β f i β‘c g i)
  β f β‘c g
funExtI p i x = p x i

pathTransport : β {P : I β Set} {A : Set} {x : A} {eqA : A β‘c P i0} {y : P i1}
  β PathP (Ξ» i β (eqA β (Ξ» j β P j)) i) x y
  β PathP P (transport eqA x) y
pathTransport pth = toPathP (symPath (transportComposite _ _ _) β fromPathP pth)

compPathTransport : β {P : I β Set} {A : Set} {x : A} {eqA : A β‘c P i0} {y : P i1}
  β {z : eqA i1}
  β PathP (Ξ» zβ β eqA zβ) x z
  β PathP P z y
  β PathP P (transport eqA x) y
compPathTransport pxz pzy = toPathP (symPath (transportComposite _ _ _) β fromPathP (compPathP pxz pzy))

data Erase {β} (A : Set β) : Prop β where
  erase : A β Erase A



-- compPathPGoal {P = P} {x = x} {z = z} {Y = Y} {y} eqxy eqyz pxy pyz =
--   let
--     cmp = compPathP pxy pyz
--   in transport (congβ {A = I β Set} {B = Ξ» P β (P i0 Γ P i1)} (Ξ» P (x , z) β PathP P x z) (funExtI (Ξ» j β {!P i!})) Ξ» _ β (x , z)) cmp
