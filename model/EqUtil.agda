module EqUtil where

open import Relation.Binary.PropositionalEquality

open import Agda.Primitive renaming (Set to Type ; Setω to Typeω)
import Cubical.Data.Equality as PEq
import Cubical.Data.Equality.Conversion  as Conv
import Cubical.Foundations.Prelude as Cubical

-- We can convert any stdlib inductive equality into a cubical one and back

--TODO rename module, not just funext

ptoc : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → x Cubical.≡ y
ptoc eq = PEq.eqToPath eq


ctop : ∀ {ℓ} {A : Type ℓ} {x y : A} → x Cubical.≡ y → x ≡ y
ctop eq = Conv.pathToEq eq


funExt : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f g : A → B}
  → (∀ x → f x ≡ g x) → f ≡ g
funExt pf =  (PEq.funExt (λ x →  (pf x)))
