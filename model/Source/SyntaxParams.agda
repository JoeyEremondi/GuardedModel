module Source.SyntaxParams where

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.FinData renaming (zero to fzero ; suc to fsuc)
open import Cubical.Data.List
open import Cubical.Data.Sum hiding (map)
open import Cubical.Foundations.Prelude
import Cubical.Data.Vec as V


--Lets us parameterize over the static, gradual, and cast calculi

data WhichGradual : Set where
  Surface Cast : WhichGradual


data SyntaxType : Set where
  Intro Lam Elim Ty Bnd SurfUnk ⁇℧Syn CastSyn  : SyntaxType

data IsTrue : Bool → Prop where
  instance isTrue : IsTrue true


record Language : Set where
  field
    inLang : WhichGradual → Bool
  InLang : WhichGradual → Prop
  InLang ty = IsTrue (inLang ty)

record Inductives : Set where
  field
    numTyCons : ℕ
  CName : Set
  CName = Fin numTyCons
  field
    numCtors : CName → ℕ
  DName : CName → Set
  DName c = Fin (numCtors c)
  field
    arityC : CName → ℕ
    numIxC : CName → ℕ
    arityD : (c : CName) → DName c → ℕ

open Inductives {{...}} public
open Language{{...}} public



allFin : (n : ℕ) → V.Vec (Fin n) n
allFin zero = V.[]
allFin (suc n) = fzero V.∷ V.map fsuc (allFin n)

Elem : ∀ {A n} → A → V.Vec A n → Set
Elem x V.[] = ⊥
Elem x (h V.∷ t) = (h ≡ x) ⊎ Elem x t

elemMap : ∀ {A B n} {f : A → B} {x : A} (l : V.Vec A n) → Elem x l → Elem (f x) (V.map f l)
elemMap {f = f} (x V.∷ l) (inl x₁) = inl (cong f x₁)
elemMap (x V.∷ l) (inr x₁) = inr (elemMap l x₁)

allIn : ∀ {n} (f : Fin n) → Elem f (allFin n)
allIn {zero} ()
allIn {suc n} fzero = inl refl
allIn {suc n} (fsuc x) = inr (elemMap (allFin n) (allIn x))



allCtors : {{_ : Inductives}} →
  (c : CName) → V.Vec (DName c) (numCtors c)
allCtors c = allFin _

CastCalc : Language
CastCalc = record { inLang = λ _ → true }
