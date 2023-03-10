


{-# OPTIONS --cubical --guarded -v term:50 #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
-- open import Cubical.Data.Equality using (_β‘p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat as Nat
import Cubical.Data.Nat.Order as Nat
import Cubical.Induction.WellFounded as Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool
-- open import Cubical.Data.Equality
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import UnkGerm
open import GuardedAlgebra
import GuardedModality as G
open import Cubical.Induction.WellFounded
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import InductiveCodes
open import W
-- open import Cubical.Data.Equality using (ptoc)

open import ApproxExact
open import GTypes
open import Code
open import Head
open import Util

open import Sizes.Size -- β El β§ Cπ refl

open import Sizes.MultiMax
open import Sizes.NatLim

-- open import InductiveCodes
open import Cubical.Foundations.Transport

module Sizes.ElSize {{_ : DataTypes}} {{_ : DataGerms}} {{_ : CodesForInductives }}
    (β : β)
    (smallerCodeSize : {{inst : 0< β}} β β-1 (SmallerCodeAt β ) β Size)
    (smallerElSize : {{Γ¦ : Γ }} β {{inst : 0< β}} β (c : β-1 (SmallerCodeAt β)) β El-1 (SmallerCodeAt β) c β Size)
    (elSizeConsumeFuel : β {{Γ¦ : Γ}} β (c : β β) β El c β Size)
  where
open import Sizes.CodeSize β smallerCodeSize

GNatSize : GNat β Size
GNatSize (GSuc x) = Sβ (GNatSize x)
GNatSize x = S1


-- germUnkSize' : (x : WUnk {{Γ¦ = Approx}} β) β Size
βSize' : β {{ Γ¦ : Γ}} β βTy β β Size
GermSize' : β {{ Γ¦ : Γ}} {tyCtor : CName} β βGermTy β tyCtor β Size
elSize' : β {{Γ¦ : Γ}} (c : β β) β El c β Size
-- βΉelSize' : β {β} (c : β β) β βΉEl c β Size
CΞΌSize' : β  {{Γ¦ : Γ}}  {tyCtor : CName} (D : DCtors β tyCtor) β  βΞΌ β tyCtor D β Size
CElSize' : β {{Γ¦ : Γ}} {tyCtor : CName} (D : DCtors β tyCtor )  β (E : DCtors β tyCtor)
  β  (cf : βFunctor β tyCtor D (βΞΌ β tyCtor E))
  β Size


βSize' ββ§ = S1
βSize' ββ = S1
βSize' βπ = S1
βSize' (ββ n) = Sβ (GNatSize n)
βSize' (βType x ) = Sβ (smallerCodeSize x)
βSize' (βCumul c x) = Sβ (smallerElSize c x)
βSize' (βΞ  f) = Sβ (SLim {β = β} Cβ Ξ» x β βSize' (f (transport (symPath  βWrapβ‘  ) (next (exact {c = Cβ {β = β}} x)))))
βSize' (βΞ£ (x , y)) = Sβ (smax (βSize' x) (βSize' y))
βSize' (ββ‘ (w β’ _ β _)) = Sβ (βSize' w)
βSize' (βΞΌ tyCtor x) = Sβ (GermSize' x)

GermSize' DataGerms.ββ§ = S1
GermSize' DataGerms.ββ = S1
GermSize' {tyCtor = tyCtor} (DataGerms.Wsup d com germFO germHO germHOUnk)
  = Sβ (smax* (elSizeConsumeFuel (germCommandCode (dataGermIsCode β tyCtor d )) (Iso.fun (germCommandIso (dataGermIsCode β tyCtor d) ) com)
              β· FinLim (Ξ» n β GermSize' (germFO n))
              β· SLim (germHOCode (dataGermIsCode β tyCtor d) (approx (Iso.fun (germCommandIso (dataGermIsCode β tyCtor d)) com))) (Ξ» r β GermSize' (germHO (Iso.inv (germHOIso (dataGermIsCode β tyCtor d) _) (exact r))))
              β· SLim (germHOUnkCode (dataGermIsCode β tyCtor d) (approx (Iso.fun (germCommandIso (dataGermIsCode β tyCtor d)) com))) (Ξ» r β βSize' (germHOUnk (Iso.inv (germHOUnkIso (dataGermIsCode β tyCtor d) _) (exact r)))) β· []))

elSize' {{Γ¦ = Γ¦}} Cβ x = βSize' {{Γ¦ = Γ¦}} x --germUnkSize' (βToW {{Γ¦ = Approx}} (approx {c = Cβ {β = β}} x))
elSize' Cβ§ x = S1
elSize' Cπ x = S1
elSize' Cπ x = S1
elSize' Cβ x = GNatSize x
elSize' (CType {{inst = inst}}) x = Sβ (smallerCodeSize x)
elSize' {{Γ¦ = Γ¦}}  (CΞ  dom cod) f = Sβ (SLim dom Ξ» x β elSize' (cod _) (f (exact x))) -- Sβ (SLim dom (Ξ» x β elSize' {{Γ¦ = Γ¦}} (substPath (Ξ» x β El (cod x)) (approxExactβ‘ x) (f (exact x))) ))
elSize' {{Γ¦ = Γ¦}} (CΞ£ dom cod) (x , y) = Sβ (smax (elSize' {{Γ¦ = Γ¦}} dom x) (elSize' {{Γ¦ = Γ¦}} (cod (approx x)) y)) -- Sβ (smax (elSize' dom (exact x)) (elSize' (cod (approx x)) y))
elSize' (Cβ‘ c x y ) (w β’ _ β _) = Sβ (elSize' {{Approx}} c w)
elSize' (CΞΌ tyCtor cI D i) x = CΞΌSize' D (toβΞΌ β tyCtor D x)
-- Sβ (smax* (elSize' (coms d) com β· (FinLim Ξ» n β elSize' {!!} (res (inl n))) β· (SLim (βCommand (D d)) Ξ» com β SLim (βHOResponse (D d) com) Ξ» x β elSize' (CΞΌ coms ress) (res (inr (exact _ x)))) β· [])) -- Sβ (CΞΌSize' D ( Iso.inv CΞΌWiso (approx {β = β} {c = CΞΌ tyCtor cI D i} x) ))
elSize' (CCumul {{inst = inst}} c) x = smallerElSize _ x --elSize' c x

CΞΌSize' D  (βinit x) = Sβ (CElSize' D D x) -- Sβ (CElSize' (D (βFunctor.d x)) D x)
CΞΌSize' D ΞΌβ = S1
CΞΌSize' D ΞΌβ§ = S1

CElSize' D E (βEl d com rFO rHO) = Sβ (smax* (elSize' _ com β· (FinLim Ξ» n β CΞΌSize' E (rFO n)) β· (SLim (βHOResponse (D d) (approx com)) Ξ» r β CΞΌSize' E (rHO (exact r))) β· []))

