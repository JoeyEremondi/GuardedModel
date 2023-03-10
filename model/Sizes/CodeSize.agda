

{-# OPTIONS --cubical --guarded -v term:50 #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
-- open import Cubical.Data.Equality using (_ā”p_ ; reflp ; cong)
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


-- open import InductiveCodes
open import Cubical.Foundations.Transport


-- Brouwer Tree ordinals
-- Based on the presentation by Kraus, Forsburg and Xu
-- https://arxiv.org/abs/2104.02549

-- The main difference is that we allow the limit over the elements of any code type, not just natural numbers

open import Code

open import Sizes.MultiMax

open import Sizes.NatLim
open import InductiveCodes
open import Head
open import Util

open import Sizes.Size -- ā El ā§ Cš refl
module Sizes.CodeSize {{_ : DataTypes}} {{_ : DataGerms}} {{_ : CodesForInductives }}
    (ā : ā)
    (smallerCodeSize : {{inst : 0< ā}} ā ā-1 (SmallerCodeAt ā ) ā Size)
    (codeSizeConsumeFuel : (c : ā ā) ā Size)
    -- (smallerElSize : {{Ć¦ : Ć }} ā {{inst : 0< ā}} ā (c : ā-1 (SmallerCodeAt ā)) ā El-1 (SmallerCodeAt ā) c ā Size)
  where







codeSize' : ā ā ā Size

-- The unknown type has a size that is larger than all other sizes
-- We hack this using limits of ordinals
-- TODO will this actually work?
codeSize' Cā = Sā (SLim {ā = ā.suc ā} CType codeSizeConsumeFuel)
codeSize' Cā§ = S1
codeSize' Cš = S1
codeSize' Cš = S1
codeSize' Cā = S1
codeSize' CType = S1
codeSize' (CĪ  dom cod) =
  Sā (smax
    ( (codeSize' dom))
    ( (SLim dom Ī» x ā  (codeSize' (cod x)))))
codeSize' (CĪ£ dom cod) =
  Sā (smax
    ( (codeSize' dom))
    (  (SLim dom Ī» x ā  (codeSize' (cod x)))))
codeSize'  (Cā” c x y) = Sā ( (codeSize' c))
codeSize' (CĪ¼ tyCtor c D x) = Sā (DLim tyCtor Ī» d ā smax (codeSize' (āCommand (D d))) (SLim (āCommand (D d)) (Ī» com ā codeSize' (āHOResponse (D d) com))))
codeSize' (CCumul {{inst = inst}} c) = Sā (smallerCodeSize c)
