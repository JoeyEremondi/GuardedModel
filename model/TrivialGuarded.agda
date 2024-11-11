module TrivialGuarded where

open import GuardedAlgebra
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude

instance
  trivialGuarded : GuardedAlgebra
  GuardedAlgebra.▹ trivialGuarded = λ _ → Unit*
  GuardedAlgebra.▸ trivialGuarded = λ _ → Unit*
  GuardedAlgebra.next trivialGuarded = λ _ → tt*
  GuardedAlgebra._⊛_ trivialGuarded = λ _ _ → tt*
  GuardedAlgebra.dfix trivialGuarded = λ _ → tt*
  GuardedAlgebra.pfix trivialGuarded = λ f → refl
  GuardedAlgebra.Dep▸ trivialGuarded = λ _ _ → tt*
  GuardedAlgebra.hollowEq trivialGuarded = refl
  GuardedAlgebra.L trivialGuarded A = A
  GuardedAlgebra.pure trivialGuarded x = x
  GuardedAlgebra._>>=_ trivialGuarded a f = f a
  GuardedAlgebra.θL trivialGuarded default _ = default
