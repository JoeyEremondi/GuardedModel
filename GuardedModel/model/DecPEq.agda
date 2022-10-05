{-# OPTIONS --cubical --guarded #-}

open import Cubical.Data.Nat
import Cubical.Data.FinData as F
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Unit
open import Cubical.Data.Bool renaming (Bool to 𝟚)
open import Cubical.Data.Sigma
open import Cubical.Data.Equality hiding (_≡⟨_⟩_ ;  _∎ )
import Cubical.Data.Equality as PEq
open import Cubical.Relation.Nullary

open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
module DecPEq where

pTrans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡p y → y ≡p z → x ≡p z
pTrans reflp reflp = reflp

pSym : ∀ {ℓ} {A : Set ℓ} {x y  : A} → x ≡p y → y ≡p x
pSym reflp = reflp

pCong : ∀ {l1 l2} {A : Set l1} {B : Set l2} {x y : A} → (f : A → B) → x ≡p y → f x ≡p f y
pCong f reflp = reflp

pCong4 : ∀ {ℓ} {A B C D E : Set ℓ} {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} {d1 d2 : D}
  → (f : A → B → C → D → E) → a1 ≡p a2 → b1 ≡p b2 → c1 ≡p c2 → d1 ≡p d2 →
  f a1 b1 c1 d1 ≡p f a2 b2 c2 d2
pCong4 f reflp reflp reflp reflp = reflp

pSubst : ∀ {l1 l2} {A : Set l1} {x y : A} → (P : A → Set l2) → x ≡p y → P x → P y
pSubst P reflp x = x

sucInj : ∀ {x y : ℕ} → suc x ≡p suc y → x ≡p y
sucInj {x} {y} reflp = reflp

fSucInj : ∀ {n : ℕ} {x y : Fin n} → F.suc x ≡p F.suc y → x ≡p y
fSucInj {x} {y} reflp = reflp

decNat : ∀ (x y : ℕ) → Dec (x ≡p y)
decNat zero zero = yes reflp
decNat zero (suc y) = no (λ ())
decNat (suc x) zero = no (λ ())
decNat (suc x) (suc y) with decNat x y
... | yes reflp = yes reflp
... | no np = no (λ p → np (sucInj p))

decFin : ∀ {n : ℕ} (x y : Fin n) → Dec (x ≡p y)
decFin F.zero F.zero = yes reflp
decFin F.zero (F.suc y) = no (λ ())
decFin (F.suc x) F.zero = no (λ ())
decFin (F.suc x) (F.suc y) with decFin x y
... | yes reflp = yes reflp
... | no npf = no (λ p → npf (fSucInj p))

decBool : ∀ (b1 b2 : 𝟚) → Dec (b1 ≡p b2)
decBool false false = yes reflp
decBool false true = no (λ ())
decBool true false = no (λ ())
decBool true true = yes reflp

natProdInj : ∀ {x1 x2 y1 y2 : ℕ} → (x1 , x2) ≡p (y1 , y2) → ((x1 ≡p y1)  × (x2 ≡p y2))
natProdInj {x1} {x2} {y1} {y2} reflp = reflp , reflp

finProdInj : ∀ {m n} {x1 y1 : Fin m} {x2 y2 : Fin n} → (x1 , x2) ≡p (y1 , y2) → ((x1 ≡p y1)  × (x2 ≡p y2))
finProdInj {x1} {x2} {y1} {y2} reflp = reflp , reflp

natProdDec : ∀ (x y : ℕ × ℕ) → Dec (x ≡p y)
natProdDec (x1 , x2) (y1 , y2) with decNat x1 y1 | decNat x2 y2
... | _ | no npf = no (λ pf → npf (snd (natProdInj pf)))
... | no npf | _ = no (λ pf → npf (fst (natProdInj pf)))
... | yes reflp | yes reflp = yes reflp

finProdDec : ∀ {m n} (x y : Fin m × Fin n) → Dec (x ≡p y)
finProdDec (x1 , x2) (y1 , y2) with decFin x1 y1 | decFin x2 y2
... | _ | no npf = no (λ pf → npf (snd (finProdInj pf)))
... | no npf | _ = no (λ pf → npf (fst (finProdInj pf)))
... | yes reflp | yes reflp = yes reflp

-- If ≡p is decidable, then so is ≡
propToPathDec : ∀ {ℓ} {X : Set ℓ} {x y : X} → x ≡p y → x ≡ y
propToPathDec reflp = reflc

pathToPropDec : ∀ {ℓ} {X : Set ℓ} {x y : X} → Dec (x ≡p y) → x ≡ y → (x ≡p y)
pathToPropDec {x = x} {y} (yes p) pc = p
pathToPropDec {x = x} {y} (no ¬p) pc with () ← ¬p (subst (x ≡p_) pc reflp)

decPropToDecPath : ∀ {ℓ} {X : Set ℓ} {x y : X} → Dec (x ≡p y) → Dec (x ≡ y)
decPropToDecPath (yes reflp) = yes reflc
decPropToDecPath (no npf) = no (λ x → npf (pathToPropDec (no npf) x))

open import Cubical.Relation.Nullary.DecidableEq

decUIPc : ∀ {ℓ} {X : Set ℓ} → (∀ (x y : X) → Dec (x ≡p y)) →  ∀ {x y : X} → (p1 p2 : x ≡ y) → p1 ≡ p2
decUIPc {X = X} allDec p1 p2 = Discrete→isSet (λ x y → decPropToDecPath (allDec x y)) _ _ p1 p2

decKc  :  ∀ {ℓ} {X : Set ℓ} → (∀ (x y : X) → Dec (x ≡p y)) →  ∀ {x : X} → (p1 : x ≡c x) → p1 ≡ reflc
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
infixr 2 _≡p⟨⟩_ _≡p⟨_⟩_
infix  3 _∎

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

_≡p⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A) {y z : A}
  → x ≡p y
  → y ≡p z
    -----
  → x ≡p z
x ≡p⟨ x≡py ⟩ y≡pz  = pTrans x≡py y≡pz

_∎ : ∀ {ℓ} {A : Set ℓ} (x : A)
     -----
  → x ≡p x
x ∎  =  reflp
module Constant⇒UIP
  {a} {A : Set a} (f : ∀ {x y : A} → x ≡p y → x ≡p y)
  (f-constant : ∀ {a b} (p q : a ≡p b) → f p ≡p f q)
  where

  trans-symˡ : ∀ {x y : A} (p : x ≡p y) → pTrans (pSym p) p ≡p reflp
  trans-symˡ reflp = reflp

  ≡-canonical : ∀ {a b : A} (p : a ≡p b) → pTrans (pSym (f reflp)) (f p) ≡p p
  ≡-canonical reflp =  trans-symˡ (f reflp)

  ≡-irrelevant : UIP A
  ≡-irrelevant p q = begin
    (p ≡p⟨ (pSym (≡-canonical p)) ⟩
    ((pTrans (pSym (f reflp)) (f p)) ≡p⟨ pCong (pTrans (pSym (f reflp)) ) (f-constant p q) ⟩
    (pTrans (pSym (f reflp)) (f q) ≡p⟨ ≡-canonical q  ⟩
    (q ∎))))
    -- p                          ≡p⟨ pSym (≡-canonical p) ⟩
    -- pTrans (pSym (f reflp)) (f p) ≡p⟨ pCong (pTrans _) (f-constant p q) ⟩
    -- pTrans (pSym (f reflp)) (f q) ≡p⟨ ≡p-canonical q ⟩
    -- q  ∎
    -- pTrans (pSym (≡p-canonical p)) (pTrans (pCong {!!} (f-constant p q)) (≡p-canonical q))


module Decidable⇒UIP
  {a} {A : Set a} (_≟_ : ∀ x y → Dec (x ≡p y))
  where

  ≡-normalise : ∀ { x y } → x ≡p y → x ≡p y
  ≡-normalise {a} {b} a≡b with a ≟ b
  ... | yes pf = pf
  ... | no npf with () ← npf a≡b

  ≡-normalise-constant : ∀ {a b} (p q : a ≡p b) → ≡-normalise p ≡p ≡-normalise q
  ≡-normalise-constant {a} {b} p q with a ≟ b
  ... | yes pf  = reflp
  ... | no npf with () ← npf p

  ≡-irrelevant : UIP A
  ≡-irrelevant = Constant⇒UIP.≡-irrelevant ≡-normalise ≡-normalise-constant

open Decidable⇒UIP renaming (≡-irrelevant to decUIP) public


uipNat : ∀ {x y : ℕ} → (p1 p2 : x ≡p y) → p1 ≡p p2
uipNat p1 p2 = Decidable⇒UIP.≡-irrelevant decNat p1 p2

uipFin : ∀ {n} {x y : Fin n} → (p1 p2 : x ≡p y) → p1 ≡p p2
uipFin p1 p2 = Decidable⇒UIP.≡-irrelevant decFin p1 p2

axKFin : ∀ {n} {x : Fin n} → (p1  : x ≡p x) → p1 ≡p reflp
axKFin p1 = Decidable⇒UIP.≡-irrelevant decFin p1 reflp



isPropP : ∀ {ℓ} {A : Set ℓ} → isSet A → ∀ {x y : A} → {p1 p2 : x ≡p y} → p1 ≡c p2
isPropP prp {p1 = p1} {p2} =  sym (Iso.rightInv p≅c p1) ∙ cong (Iso.fun p≅c) p12 ∙ Iso.rightInv p≅c p2
  where
    p12 : Iso.inv p≅c p1 ≡ Iso.inv p≅c p2
    p12 = prp _ _ (Iso.inv p≅c p1) (Iso.inv p≅c p2)
