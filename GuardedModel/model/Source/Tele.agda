{-# OPTIONS --rewriting #-}


open import Source.SyntaxParams
open import Cubical.Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Equality
open import Cubical.Data.Nat.Order

module Source.Tele {{lang : Language}} {{ _ : Inductives }}  where
open import Source.Syntax


data MaxVarIs (T : AST) : ℕ → Prop where
  maxVarIs : ∀ {n} → n ≡p (max-var (AST→ABT T)) →  MaxVarIs T n


IsClosed : AST → Prop
IsClosed T = MaxVarIs T 0


teleLam : ∀ {n} → (Γ : Vec AST n) → (body : AST) → AST
teleLam [] body = body
teleLam (T ∷ Γ) body = teleLam Γ (λx⦂ T ∙ body)

ClosedOver : ∀ {n} → Vec AST n → AST → Prop
ClosedOver Γ t = IsClosed (teleLam Γ t)


data TeleScoped : ∀ {n} → (Γ : Vec AST n) → Prop where
  instance TeleNil : TeleScoped []
  instance TCons : ∀ {n} {T} {Γ : Vec AST n} → {{_ : TeleScoped Γ}} → {{_ : ClosedOver Γ T}} → TeleScoped (T ∷ Γ)

record Tele (n : ℕ) : Set where
  constructor tele
  field
    elems : Vec AST n
    {{wellScoped}} : TeleScoped elems


open Tele public

record Term {n} (Γ : Tele n) : Set where
  constructor tm
  field
    theTerm : AST
    {{wellScoped}} : ClosedOver (elems Γ) theTerm

∙ : Tele 0
∙ = record { elems = [] }

_,,[x⦂_] : ∀ {n} → (Γ : Tele n) → Term Γ → Tele (suc n)
Γ ,,[x⦂ (tm T) ] = record { elems = T ∷ Tele.elems Γ }


-- lookupClosed : ∀  {n} → (Γ : Tele n) → (x : Fin n) → ClosedOver (Tele.elems Γ) (lookup x (Tele.elems Γ))
-- lookupClosed (tele (t ∷ rest) ⦃ TCons {Γ = _} ⦃ sc ⦄ ⦃ maxVarIs x ⦄ ⦄) zero = maxVarIs {!!}
-- lookupClosed Γ (suc x) = {!!}

-- lookupEnv : ∀ {n} → (Γ : Tele n) → Fin n → Term Γ
-- lookupEnv Γ n with t ← lookup n (Tele.elems Γ) = tm t ⦃ {!!} ⦄



open Term public


record IndParams : Set where
  field
    paramTypes : (c : CName) → Vec AST (arityC c)
    indexTypes : (c : CName) →  Vec AST (numIxC c)
    argTypes : ∀ {c : CName} → (d : DName c) → Vec AST (arityD c d)

open IndParams {{...}} public
