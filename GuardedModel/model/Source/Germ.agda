{-# OPTIONS --rewriting #-}

open import Source.SyntaxParams
open import Cubical.Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Equality
open import Cubical.Data.Nat.Order

open import Source.Tele {{CastCalc}}

module Source.Germ {{ _ : Inductives }} {{_ : IndParams}} where

open import Source.Syntax {{CastCalc}}
open import Source.Sub

Germ : OpI Ty → ℕ →  AST
TeleGerm : ∀ {n} → Vec AST n → Vec AST n

Germ (OType x) i = SType i
Germ OΠ i = [x⦂ ⁇[ SType i ] ]⟶ ⁇[ SType i ]
Germ (OC c j) i = SC c i (TeleGerm (paramTypes c ++ indexTypes c))
Germ O≡ i = ⁇[ ⁇[ SType i ]  ] ≡[ ⁇[ SType i ]  ] ⁇[ ⁇[ SType i ]  ]

--TODO check to make sure don't need a reverse or something
TeleGerm [] = []
TeleGerm (T ∷ Γ) = ⁇[ [ subFirstN rec /x⃗] T ] ∷ rec
 where
   rec = TeleGerm Γ
