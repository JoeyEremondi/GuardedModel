--
{-# OPTIONS --rewriting #-}


open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Source.SyntaxParams

module Source.SubProperties {{_ : Inductives}} where

open import Source.Sub

open import DecPEq
open import Cubical.Data.Nat
open import Source.Syntax {{CastCalc}}
open import Cubical.Data.Equality hiding (Sub)

-- open import Syntax using (Sig ; ν ;  ■ )

open import Cubical.Data.List as List hiding ([_])
open import Cubical.Data.Vec as Vec


-- import Map Op sig as Map
-- Helpful rules for our custom operations

open import Source.Sub


{-# REWRITE extNPush #-}

--------------------------------

-- Helpful for reducing the number of cases we need to write
subWhich : ∀ {sub : Subst} {which T} → ABT→AST (⟪ sub ⟫ (AST→ABT ⁇or℧[ which ][ T ]))  ≡p ⁇or℧[ which ][ ABT→AST ( ⟪ sub ⟫ (AST→ABT T)) ]
subWhich {which = O⁇} = reflp
subWhich {which = O℧} = reflp

subReplace : ∀ {m} {n} {sub : Subst} {v1 : Vec AST m} {v2 : Vec AST n} →
  fromRepeat (⟪ sub ⟫₊ (toRepeat (v1 Vec.++ v2)) ) ≡p fromRepeat ( ⟪ sub ⟫₊ (toRepeat v1) ) Vec.++ fromRepeat ( ⟪ sub ⟫₊ (toRepeat v2) )
subReplace {v1 = []} = reflp
subReplace {sub = sub} {v1 = x ∷ v1} {v2 = v2} = pCong (λ x → _ ∷ x) (subReplace {sub = sub} {v1 = v1})

subFromRepeat : ∀  {n} {sub : Subst} {v : Vec AST n} →
  fromRepeat (⟪ sub ⟫₊ (toRepeat v) ) ≡p Vec.map (λ t → [  sub /x⃗] t) v
subFromRepeat {.zero} {sub} {[]} = reflp
subFromRepeat {.(suc _)} {sub} {x ∷ v} = pCong (λ x → _ ∷ x) (subFromRepeat {sub = sub} {v = v})


subFromArgs : ∀  {n} {sub : Subst} {sigs : Vec Sig n} {v : Vec AST n}  →
  argsToVec ( ⟪ sub ⟫₊ (argsFromVec sigs v)) (toListLen sigs)   ≡p Vec.zipWith (λ sg t → fromArg {sig = sg} ( ⟪ sub ⟫ₐ (toArg {sig = sg} t))) sigs v
subFromArgs {sigs = []} {v = []}  = reflp
subFromArgs {sub = sub} {sigs = s ∷ sigs} {v = x ∷ v} rewrite uipNat (suc-inj (toListLen (s ∷ sigs)) ) (toListLen sigs)  = pCong (λ x → _ ∷ x) (subFromArgs {sub = sub} {sigs = sigs} {v = v})

vecMap : ∀ {m n} {f : AST → AST} → (v1 : Vec AST m) → (v2 : Vec AST n) → Vec.map f (v1 Vec.++ v2) ≡p (Vec.map f v1) Vec.++ (Vec.map f v2)
vecMap [] v2 = reflp
vecMap {f = f} (x ∷ v1) v2 = pCong (λ x → _ ∷ x) (vecMap {f = f} v1 v2)



{-# REWRITE subWhich #-}
{-# REWRITE subReplace #-}
{-# REWRITE subFromRepeat #-}
{-# REWRITE subFromArgs #-}
{-# REWRITE vecMap #-}



subFirstNComp : ∀ {n} sub → (v : Vec AST n) →  subFirstN v ⨟ sub ≡p extN n sub ⨟ subFirstN (Vec.map [ sub /x⃗] v)
subFirstNComp sub [] = reflp
subFirstNComp {suc n} sub (t ∷ v) = pCong (λ x → ([ sub /x⃗] t) ∘ x) (subFirstNComp sub v)



{-# REWRITE subFirstNComp #-}


-- subExtComp :  ∀ {n} sub → (v : Vec AST n) → extN n sub ⨟ subFirstN v ≡p subFirstN v
-- subExtComp sub v = pSym {!subFirstNComp v !}



zipWithMap : ∀ {l1 l2 l3 l4} {A : Set l1} {B : Set l2} {C : Set l3} {D : Set l4} →
  (f : A → B → C) (g : D → A) → ∀ {n} {v : Vec D n} {v'} →  Vec.zipWith f (Vec.map g v) v' ≡p Vec.zipWith (λ x y → f (g x) y) v v'
zipWithMap f g {v = []} {v' = []} = reflp
zipWithMap f g {v = x ∷ v} {v' = x' ∷ v'} = pCong (λ x → _ ∷ x) (zipWithMap f g)


-- multiBoundSub : ∀ n t sub → ⟪ abtSub sub ⟫ₐ (toArg {sig = nBinds n} t) ≡p toArg {sig = nBinds n} ([ extN n sub /x⃗] t)
multiBoundSub : ∀ n t sub → ⟪ sub ⟫ₐ (toArg t) ≡p toArg {sig = nBinds n} ([ extN n sub /x⃗] t)
multiBoundSub zero t sub = reflp
multiBoundSub (suc n) t sub  = begin
  ⟪  sub ⟫ₐ (bind (toArg {sig = nBinds n} t)) ≡p⟨⟩
  (bind (⟪  (ext sub) ⟫ₐ (toArg {sig = nBinds n} t))) ≡p⟨ pCong bind (multiBoundSub n t (ext sub)) ⟩
  bind (toArg {sig = nBinds n} ([ extN n (ext sub) /x⃗] t)) ≡p⟨⟩
  toArg ([ extN (suc n) sub /x⃗] t) DecPEq.∎


{-# REWRITE multiBoundSub #-}


-- subInInd : ∀ {c i T t } rhses sub → [ sub /x⃗] (Sind c i t T rhses) ≡p (Sind c i ([ sub /x⃗] t) ([ ext sub /x⃗] T) (zipWith (λ d rhs → [ extN (1 + (numIxC c + arityD c d)) sub /x⃗] rhs) (allCtors c) rhses ))
-- subInInd {c = c} rhses sub = {!reflp!}
  -- pCong (λ x → Sind _ _ _ _ x)
  -- (pTrans
  --   (zipWithMap _ _)
  --   (pCong (λ x → zipWith x (allCtors c) rhses)
  --   (Syntax.extensionality (λ d → Syntax.extensionality (λ rhs →
  --     pTrans
  --       (pCong {x = bind (⟪ _ ⟫ₐ (toArg rhs))} {y = toArg ([ extN (1 + (numIxC c + arityD c d)) sub /x⃗] rhs)} fromArg (multiBoundSub (1 + (numIxC c + arityD c d)) rhs sub))
  --       (argFromTo {sig = nBinds (1 + (numIxC c + arityD c d))} _)
  --     )))))

-- subInMultiBoundCommute : ∀ {n} sub (v : Vec AST n) → (subFirstN v) ⨟ sub ≡p (extN n sub) ⨟ (subFirstN (Vec.map [ sub /x⃗] v))


-- -- subFirstNCommute : ∀ {n} sub (v : Vec AST n) →
