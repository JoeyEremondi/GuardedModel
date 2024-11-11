module ErasedCompatiblePath where

open import Relation.Binary.PropositionalEquality

open import Agda.Primitive renaming (Set to Type ; Setω to Typeω)
open import Data.Product
import Cubical.Data.Equality as PEq
import Cubical.Data.Equality.Conversion  as Conv
open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 ) public
open import Agda.Builtin.Cubical.Path renaming (_≡_ to _≡c_) public

-- Duplicate the core Cubical definitions without using glue
-- So we can used them in an erased context

reflc : ∀ {ℓ} {A : Type ℓ} {x : A} → x ≡c x
reflc {x = x} _ = x

-- This is just too handy to not have, maybe it's in the stdlib
-- TODO check
transport :  ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A → B
transport refl x = x

-- transport is a special case of transp
transportc :  ∀ {ℓ} {A B : Type ℓ} → A ≡c B → A → B
transportc p a = transp (λ i → p i) i0 a

transportc⁻ : ∀ {ℓ} {A B : Type ℓ} → A ≡c B → B → A
transportc⁻ p = transportc (λ i → p (~ i))

cJ : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A}
  (P : ∀ y → x ≡c y → Type ℓ') (d : P x reflc) (p : x ≡c y) → P y p
cJ P d p = transportc (λ i → P (p i) (λ j → p (i ∧ j))) d

pathToEq : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡c y → x ≡ y
pathToEq {x = x} = cJ (λ y _ → x ≡ y) refl

-- We can convert any stdlib inductive equality into a cubical one and back

--TODO rename module, not just funext

ptoc : ∀ {ℓ} {A : Type ℓ} {x y : A} → ( eq : x ≡ y) → x ≡c y
ptoc {x = x} refl = reflc



ctop : ∀ {ℓ} {A : Type ℓ} {x y : A} → (eq : x ≡c y) → x ≡ y
ctop eq  = pathToEq eq


-- Characterization of paths in Σ using dependent paths

-- Cubcial just handles Sigma eq so well
-- but we make it work with normal pairs

module _ {ℓ ℓ'} {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
  {x : Σ (A i0) (B i0)} {y : Σ (A i1) (B i1)}
  where

  ΣPathP : Σ[ p ∈ PathP A (proj₁ x) (proj₁ y) ] PathP (λ i → B i (p i)) (proj₂ x) (proj₂ y)
         → PathP (λ i → Σ (A i) (B i)) x y
  ΣPathP eq i = proj₁ eq i , proj₂ eq i


  ΣPathP' : ( p : PathP A (proj₁ x) (proj₁ y) )
         → PathP (λ i → B i (p i)) (proj₂ x) (proj₂ y)
         → PathP (λ i → Σ (A i) (B i)) x y
  ΣPathP' eqx eqy = ΣPathP (eqx , eqy)
