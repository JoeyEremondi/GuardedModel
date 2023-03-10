-- Inductive Descriptions for Gradual Datatypes

open import Level
open import Cubical.Data.Nat renaming (Unit to π)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty renaming (β₯ to π)
open import Cubical.Relation.Nullary
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Bool renaming (Bool to π)
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Sum as Sum
open import Cubical.Data.FinData
-- Bool is the gradual unit type, true is tt and false is β§

open import Cubical.Data.Sum
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
open import DecPEq
open import Cubical.Functions.FunExtEquiv using (funExtDep)

-- open import Cubical.Data.Bool
open import GuardedAlgebra
import GuardedModality as G

open import ApproxExact
open import Util
module W where

record Container (I : Set)  : Set1 where
  constructor _β_/_
  field
    Command  : (i : I) β Set
    Response : β {i} β Command i β Set
    -- ResponseΓ : β {i} β Command i β Set
    -- ResponseUnk : β {i} β Command i β Set
    inext     : β {i} (c : Command i) β Response c β I

open Container public


record β¦_β§F {I} (C : Container I) (X : I β Set) (i : I) : Set where
  constructor FC
  field
    command : Command C i
    response :
      (r : Response C command)
      β X (inext C command r)
    -- responseLater :
    --   (r : Response C command)
    --   β β j
    --   β j β inext C command r
    --   β LΓ (X j)
    -- responseUnk : ResponseUnk C command β Unk

-- Functoral action aka good old map
FMap : β {I} {C : Container I} {X Y : I β Set} {i : I} β (β {i} β X i β Y i) β β¦ C β§F X i β β¦ C β§F Y i
FMap f (FC com resp) = FC com (Ξ» r β f (resp r))

-- TODO : can't implement the full traversals until we have meet for indices
β‘ : β {β I} {X : I β Set} (C : Container I) β  ((Ξ£ I X) β Set β) β (Ξ£ I (β¦ C β§F X)) β Set β
β‘ C P (i , (FC c k)) = β r β P (inext C c r , k r)

data WΜ {I : Set} (C : Container I) (i : I)  :  Set where
  Wsup : β¦ C β§F  (WΜ C) i β WΜ C i
  Wβ§ Wβ : WΜ C i
  -- Projections.


-- Given a container for each a : A, produce the new container
-- that is the sum of all those containers.
-- Useful for encoding data constructors encoded as Fin
Arg : β {A I : Set} β (A β Container I) β Container I
Command (Arg {A} f) i = Ξ£[ a β A ] Command (f a) i
Response (Arg f) (a , com) = Response (f a) com
inext (Arg f) (a , com) r = inext (f a) com r
