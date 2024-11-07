{-# OPTIONS --cubical #-}
open import Cubical.Data.Nat
import Cubical.Data.FinData as F
open import Cubical.Data.FinData using (Fin ; discreteFin)
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Sigma hiding (_≡_)
import Cubical.Data.Equality as PEq
open import Cubical.Relation.Nullary

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
module DecPEq where

open import Cubical.Foundations.Prelude renaming (refl to reflc ; _≡_ to _≡c_) public
open import Agda.Builtin.Equality renaming (_≡_ to _≡p_ ;  refl to prefl ) public
import Cubical.Data.Equality  renaming (_∙_ to trans; ap to cong) -- hiding (_≡_ ; refl ; J) renaming (_≡⟨_⟩_ to _≡p⟨_⟩_  ;  _∎ to _∎p ; _∙_ to pTrans ; sym to PEq.sym ; ap to pCong ; funExt to pFunExt ; transport to pTransport ; isContr to pIsContr ; isProp to pIsProp ; isPropIsContr to pIsProPContr) public


pCong4 : ∀ {ℓ} {A B C D E : Set ℓ} {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} {d1 d2 : D}
  → (f : A → B → C → D → E) → a1 ≡p a2 → b1 ≡p b2 → c1 ≡p c2 → d1 ≡p d2 →
  f a1 b1 c1 d1 ≡p f a2 b2 c2 d2
pCong4 f PEq.refl PEq.refl PEq.refl PEq.refl = PEq.refl

pSubst : ∀ {l1 l2} {A : Set l1} {x y : A} → (P : A → Set l2) → x ≡p y → P x → P y
pSubst P PEq.refl x = x

pDec : ∀ {ℓ} {X : Set ℓ} {x y : X} → Dec (x ≡c y) → Dec (x ≡p y)
pDec (yes p) = yes (PEq.pathToEq p)
pDec (no ¬p) = no (λ pf → ¬p (PEq.eqToPath pf))

-- sucInj : ∀ {x y : ℕ} → suc x ≡p suc y → x ≡p y
-- sucInj {x} {y} PEq.refl = PEq.refl

-- fSucInj : ∀ {n : ℕ} {x y : Fin n} → F.suc x ≡p F.suc y → x ≡p y
-- fSucInj {x} {y} PEq.refl = PEq.refl

decNat : ∀ (x y : ℕ) → Dec (x ≡p y)
decNat _ _ = pDec (discreteℕ _ _)


decFin : ∀ {n : ℕ} (x y : Fin n) → Dec (x ≡p y)
decFin _ _ = pDec (discreteFin _ _)

decBool : ∀ (b1 b2 : Bool) → Dec (b1 ≡p b2)
decBool false false = yes PEq.refl
decBool false true = no (λ ())
decBool true false = no (λ ())
decBool true true = yes PEq.refl

-- natProdInj : ∀ {x1 x2 y1 y2 : ℕ} → (x1 , x2) ≡p (y1 , y2) → ((x1 ≡p y1)  × (x2 ≡p y2))
-- natProdInj {x1} {x2} {y1} {y2} PEq.refl = PEq.refl , PEq.refl

-- finProdInj : ∀ {m n} {x1 y1 : Fin m} {x2 y2 : Fin n} → (x1 , x2) ≡p (y1 , y2) → ((x1 ≡p y1)  × (x2 ≡p y2))
-- finProdInj {x1} {x2} {y1} {y2} PEq.refl = PEq.refl , PEq.refl

natProdDec : ∀ (x y : ℕ × ℕ) → Dec (x ≡p y)
natProdDec _ _ = pDec (discreteΣ discreteℕ (λ _ → discreteℕ) _ _)

finProdDec : ∀ {m n} (x y : Fin m × Fin n) → Dec (x ≡p y)
finProdDec _ _ = pDec (discreteΣ discreteFin (λ _ → discreteFin) _ _)

-- -- If ≡p is decidable, then so is ≡
propToPathDec : ∀ {ℓ} {X : Set ℓ} {x y : X} → x ≡p y → x ≡c y
propToPathDec PEq.refl = reflc

pathToPropDec : ∀ {ℓ} {X : Set ℓ} {x y : X} → Dec (x ≡p y) → x ≡c y → (x ≡p y)
pathToPropDec {x = x} {y} (yes p) pc = p
pathToPropDec {x = x} {y} (no ¬p) pc with () ← ¬p (subst (x ≡p_) pc PEq.refl)

decPropToDecPath : ∀ {ℓ} {X : Set ℓ} {x y : X} → Dec (x ≡p y) → Dec (x ≡c y)
decPropToDecPath (yes PEq.refl) = yes reflc
decPropToDecPath (no npf) = no (λ x → npf (pathToPropDec (no npf) x))

-- open import Cubical.Relation.Nullary.DecidableEq

decUIPc : ∀ {ℓ} {X : Set ℓ} → (∀ (x y : X) → Dec (x ≡p y)) →  ∀ {x y : X} → (p1 p2 : x ≡c y) → p1 ≡c p2
decUIPc {X = X} allDec p1 p2 = Discrete→isSet (λ x y → decPropToDecPath (allDec x y)) _ _ p1 p2

decKc  :  ∀ {ℓ} {X : Set ℓ} → (∀ (x y : X) → Dec (x ≡p y)) →  ∀ {x : X} → (p1 : x ≡c x) → p1 ≡c reflc
decKc allDec p1 = decUIPc allDec p1 reflc

-- Taken from Agda stdlib

UIP : ∀ {a} (A : Set a) → Set a
UIP A = ∀ {x y : A} → (p1 p2 : x ≡p y) → p1 ≡p p2

------------------------------------------------------------------------
-- Properties

-- UIP always holds when using axiom K
-- (see `Axiom.UniquenessOfIdentityProofs.WithK`).

-- The existence of a constant function over proofs of equality for
-- elements in A is enough to prove UIP for A. Indeed, we can relate any
-- proof to its image via this function which we then know is equal to
-- the image of any other proof.


infix  1 begin_

begin_ : ∀ {ℓ} {A : Set ℓ} {x y : A}
  → x ≡p y
    -----
  → x ≡p y
begin x≡py  =  x≡py

_≡p⟨⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A) {y : A}
  → x ≡p y
    -----
  → x ≡p y
x ≡p⟨⟩ x≡py  =  x≡py

-- _≡p⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A) {y z : A}
--   → x ≡p y
--   → y ≡p z
--     -----
--   → x ≡p z
-- x ≡p⟨ x≡py ⟩ y≡pz  = pTrans x≡py y≡pz

module Constant⇒UIP
  {a} {A : Set a} (f : ∀ {x y : A} → x ≡p y → x ≡p y)
  (f-constant : ∀ {a b} (p q : a ≡p b) → f p ≡p f q)
  where

  trans-symˡ : ∀ {x y : A} (p : x ≡p y) → PEq.trans (PEq.sym p) p ≡p PEq.refl
  trans-symˡ PEq.refl = PEq.refl

  ≡-canonical : ∀ {a b : A} (p : a ≡p b) → PEq.trans (PEq.sym (f PEq.refl)) (f p) ≡p p
  ≡-canonical PEq.refl =  trans-symˡ (f PEq.refl)

  ≡-irrelevant : UIP A
  ≡-irrelevant p q = begin
    (p PEq.≡⟨ (PEq.sym (≡-canonical p)) ⟩
    ((PEq.trans (PEq.sym (f PEq.refl)) (f p)) PEq.≡⟨ PEq.cong (PEq.trans (PEq.sym (f PEq.refl)) ) (f-constant p q) ⟩
    (PEq.trans (PEq.sym (f PEq.refl)) (f q) PEq.≡⟨ ≡-canonical q  ⟩
    (q PEq.∎))))


module Decidable⇒UIP
  {a} {A : Set a} (_≟_ : ∀ x y → Dec (x PEq.≡ y))
  where

  ≡-normalise : ∀ { x y } → x PEq.≡ y → x PEq.≡ y
  ≡-normalise {a} {b} a≡b with a ≟ b
  ... | yes pf = pf
  ... | no npf with () ← npf a≡b

  ≡-normalise-constant : ∀ {a b} (p q : a PEq.≡ b) → ≡-normalise p PEq.≡ ≡-normalise q
  ≡-normalise-constant {a} {b} p q with a ≟ b
  ... | yes pf  = PEq.refl
  ... | no npf with () ← npf p

  ≡-irrelevant : UIP A
  ≡-irrelevant = Constant⇒UIP.≡-irrelevant ≡-normalise ≡-normalise-constant

open Decidable⇒UIP renaming (≡-irrelevant to decUIP) public


uipNat : ∀ {x y : ℕ} → (p1 p2 : x PEq.≡ y) → p1 PEq.≡ p2
uipNat p1 p2 = Decidable⇒UIP.≡-irrelevant decNat p1 p2

uipFin : ∀ {n} {x y : Fin n} → (p1 p2 : x PEq.≡ y) → p1 PEq.≡ p2
uipFin p1 p2 = Decidable⇒UIP.≡-irrelevant decFin p1 p2

axKFin : ∀ {n} {x : Fin n} → (p1  : x PEq.≡ x) → p1 PEq.≡ PEq.refl
axKFin p1 = Decidable⇒UIP.≡-irrelevant decFin p1 PEq.refl

ctop = PEq.eqToPath
ptoc = PEq.pathToEq

isPropP : ∀ {ℓ} {A : Set ℓ} → isSet A → ∀ {x y : A} → {p1 p2 : x PEq.≡ y} → p1 ≡c p2
isPropP prp {p1 = p1} {p2} =  sym (Iso.rightInv PEq.PathIsoEq p1) ∙ cong (Iso.fun PEq.PathIsoEq) p12 ∙ Iso.rightInv PEq.PathIsoEq p2
  where
    p12 : PEq.eqToPath p1 ≡c PEq.eqToPath p2
    p12 = prp _ _ (Iso.inv PEq.PathIsoEq p1) (Iso.inv PEq.PathIsoEq p2)
