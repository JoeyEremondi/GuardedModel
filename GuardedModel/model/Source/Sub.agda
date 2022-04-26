{-# OPTIONS --rewriting #-}
open import Source.SyntaxParams

module Source.Sub  {{_ : Inductives}}  where

open import DecPEq
open import Cubical.Data.Nat
open import Source.Syntax {{CastCalc}}
open import Cubical.Data.Equality hiding (Sub)

open import Syntax using (Sig ; ν ;  ■ )

open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Vec as Vec

Name : Set
Name = ℕ


--Substitution for all variables
[_/x⃗] : Subst -> AST -> AST
[ t⃗ /x⃗] t₂ = ABT→AST (⟪ t⃗ ⟫ (AST→ABT t₂))


_∘_ : AST → Subst → Subst
t ∘ σ = (AST→ABT t) • σ

-- Substitute (consume) the first bound variable
[_/x]_ : AST -> AST -> AST
[ t /x] t₂ = [ t ∘ id  /x⃗] t₂

-- Replace the first bound variable x0 with a AST possibly containing x0
[_/x0]_ : AST -> AST -> AST
[ t /x0] t₂ = [  t ∘ ↑1 /x⃗] t₂
-- ABT→AST ( ⟪ AST→ABT t Syntax.• Syntax.↑ 1 ⟫ (AST→ABT t₂) )

-- GsubFirstN : ∀ {n} → Vec ABT n → (ℕ → ABT)
-- GsubFirstN [] = Syntax.id
-- GsubFirstN (x ∷ ts) = x Syntax.• (GsubFirstN ts)


subFirstN : ∀ {n} → Vec.Vec AST n → Subst
subFirstN [] = id
subFirstN (t ∷ v) =  t ∘ subFirstN v

subIn : AST → Subst → AST
subIn t sub = [ sub /x⃗] t

-- apply : Sub → Name → AST
-- apply s nm = ABT→AST (abtSub s nm)

weaken : AST -> AST
weaken t = [ ↑1 /x⃗] t


x0 = Svar 0


extN : ℕ → Subst → Subst
extN zero sub = sub
extN (suc n) sub = ext (extN n sub)

extNPush : ∀ n sub → extN n (ext sub) ≡p extN (suc n) sub
extNPush zero sub = reflp
extNPush (suc n) sub = pCong ext (extNPush n sub)



sub-dist' : ∀ σ₁ σ₂ M → (M • σ₁) ⨟ σ₂ ≡p ( ⟪  σ₂ ⟫ M ) • (σ₁ ⨟ σ₂)
sub-dist' = sub-dist


-- {-# REWRITE sub-dist' #-}
