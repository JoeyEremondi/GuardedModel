
-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_ā”p_ ; reflp ; cong)
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

module ValuePrec {{_ : DataTypes}} {{_ : DataGerms}} {{_ : InductiveCodes}} {{_ : DataGermsSmaller}} where

open import Code
open import Head
open import Util
open import Ord
-- open Ord ā El ā§ Cš refl


open import Germ


record SizedPrec (cSize : Ord) : Set1 where
  field
    oāc : ā {{_ : Ć}} {ā}
      ā (cā cā : ā ā)
      ā {@(tactic default (reflp {A = Ord} {cSize})) pf : omax (codeSize cā) (codeSize cā) ā”p cSize}
      ā Set
    oāv : ā {{_ : Ć}} {ā} {cā cā : ā ā} {pf}
      ā El cā
      ā El cā
      ā oāc cā cā {pf}
      ā Set

open SizedPrec

record PrecModule (cSize : Ord) : Set1 where
  field
    self : ā {size' : Ord} ā size' <o cSize ā SizedPrec size'
  _ā_oBy_SizeL_SizeR_ : ā {{_ : Ć}} {ā} {c'1 c'2}
    ā (cā cā : ā ā)
    ā  omax (codeSize c'1) (codeSize c'2) ā”p cSize
    ā (codeSize cā <o codeSize c'1)
    ā (codeSize cā <o codeSize c'2)
    ā Set
  cā ā cā oBy pf SizeL lt1 SizeR lt2 = oāc (self ?) cā cā
  interleaved mutual
    data _ā_By_ {{_ : Ć}} {ā}
      : (cā cā : ā ā)
      ā omax (codeSize cā) (codeSize cā) ā”p cSize
      ā Set
    data _ā_ā¦_  {{_ : Ć}} {ā}
      : ā {cā cā : ā ā} {pf}
      ā El cā
      ā El cā
      ā cā ā cā By pf
      ā Set
    data _ where
      āā : ā {c pf} ā c ā Cā By pf
  sizedPrec : SizedPrec cSize
  sizedPrec = record { oāc = Ī» cā cā {pf} ā cā ā cā By pf  ; oāv = Ī» v1 v2 cā ā v1 ā v2 ā¦ cā }
