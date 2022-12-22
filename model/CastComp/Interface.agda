
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Sum
import Cubical.Data.Empty as Empty
-- open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
-- open import Cubical.Data.Equality
open import UnkGerm
open import GuardedAlgebra
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude

open import ApproxExact
open import InductiveCodes
open import Sizes
-- open import CodePair

module CastComp.Interface {{_ : DataTypes}} {{_ : DataGerms}} {{_ : CodesForInductives}}   where

open import Code
open import Head
open import Util
open import WellFounded
-- open Ord ℂ El ℧ C𝟙 refl
open import Cubical.Data.FinData.Properties as Fin
import Cubical.Data.Nat.Order as Nat

import GuardedModality as ▹Mod
open import Cubical.Data.Sum

open import Assumption

mutual
  ⁇Flag : Set
  ⁇Flag = Fin 3

  ⁇any : ⁇Flag
  ⁇any = Fin.suc (Fin.suc Fin.zero)

  ⁇pos : ⁇Flag
  ⁇pos = (Fin.suc Fin.zero)

  ⁇none : ⁇Flag
  ⁇none = Fin.zero

  _<Flag_ : ⁇Flag → ⁇Flag → Set
  _<Flag_ = <Fin _

  ⁇FlagWellFounded : WellFounded _<Flag_
  ⁇FlagWellFounded = FinWellFounded

  ⁇match : (x : ⁇Flag) → (x ≡p ⁇any) ⊎ ((x ≡p ⁇pos) ⊎ (x ≡p ⁇none))
  ⁇match Fin.zero = inr (inr reflp)
  ⁇match (Fin.suc Fin.zero) = inr (inl reflp)
  ⁇match (Fin.suc (Fin.suc Fin.zero)) = inl reflp

  pos<any : ⁇pos <Flag ⁇any
  pos<any = 0 , reflc
  none<any : ⁇none <Flag ⁇any
  none<any = 1 , reflc
  none<pos : ⁇none <Flag ⁇pos
  none<pos = 0 , reflc

  open import Cubical.Data.Bool

  isPos𝔹 : ⁇Flag → Bool
  isPos𝔹 Fin.zero = false
  isPos𝔹 (Fin.suc Fin.zero)  = true
  isPos𝔹 (Fin.suc (Fin.suc Fin.zero)) = false

  if¬Pos : ⁇Flag → Set → Set → Set
  if¬Pos x A B = if isPos𝔹 x then B else A

  notPos : ⁇Flag → Set
  notPos x = isPos𝔹 x ≡p false


  depIfPos : ∀ {A B : Set} → (x : ⁇Flag) → (notPos x → A) → (x ≡p ⁇pos → B) → if¬Pos x A B
  depIfPos Fin.zero a b = a reflp
  depIfPos (Fin.suc Fin.zero) a b = b reflp
  depIfPos (Fin.suc (Fin.suc Fin.zero)) a b = a reflp


  isPropNotPos : ∀ {x} → isProp (notPos x)
  isPropNotPos  x y =  (isPropP isSetBool)


-- The tuple of things that are decreasing in our recursive calls
-- (A) Bool: flag for whether we're allowed to see ⁇ as a type
--  this is there for strict positivity: we get an extra recursive call when computing meet or cast of terms in the germ of an inductive type
--  because we're guaranteed that, within an inductive type, we never see unguarded ⁇ to the left of an arrow (because of strict positivity).
--  This lets us do induction on the size of the value for everything but functions, where we know we're not seeing ⁇
-- (B) ℕ: the universe level we're currently in. We need this so that, when (c  = CType) and (v1 v2 : El c), for the meet of v1 and v2, we can call codeMeet
--    at the smalelr universe, letting us move the size of the value into the code value
-- (C) Code size: the size of the code, either being combined with code meet, or the code of the values being cast/composed
-- (D) Value size: the size of the value currently being operated on. Set to S0 for codeMeet.
CastCompMeasure : Set
CastCompMeasure = ℕ × ⁇Flag × Size

-- We can define the lexicographic-ordering on this measure
_<CastComp_ : (m1 m2 : CastCompMeasure) → Set
_<CastComp_ = _<Lex_ {_<a_ = Nat._<_} {_<b_ = _<Lex_ {_<a_ = _<Flag_}  {_<b_ = _<ₛ_}}

CastCompWellFounded : WellFounded (λ x y → ∥ x <CastComp y ∥₁)
CastCompWellFounded = ∥LexWellFounded∥ Nat.<-wellfounded (LexWellFounded ⁇FlagWellFounded sizeWF)

open import Germ
record SizedCastMeet (⁇Allowed : ⁇Flag) (ℓ : ℕ) (size : Size) : Set where
  field

    o⁇ : ∀ {{æ : Æ}}
      → notPos ⁇Allowed
      → (c : ℂ ℓ)
      → (pfc1 : codeSize c ≡p size )
      → (El c)

    oMeet : ∀ {{æ : Æ}}
      → (c : ℂ ℓ)
      → (x y : El c)
      → ( pfc : if¬Pos ⁇Allowed
        ((codeSize c)  ≡p size)
        (smax (elSize c x) (elSize c y)  ≡p size) )
      → LÆ (El c)

    oDataGermMeet : ∀ {{æ : Æ}} {tyCtor}
      → (x y : ⁇GermTy ℓ tyCtor)
      → smax (GermSize x) (GermSize y) ≡p size
      → LÆ (⁇GermTy ℓ tyCtor)


    oCodeMeet :
      notPos ⁇Allowed
      → (c1 c2 : ℂ ℓ)
      → ( pfc1 : smax (codeSize c1) (codeSize c2)  ≡p size )
      → (ℂ ℓ)

    oCodeMeetSize :
      (np : notPos ⁇Allowed)
      → (c1 c2 : ℂ ℓ)
      → ( pfc1 : smax (codeSize c1) (codeSize c2)  ≡p size )
      → codeSize (oCodeMeet np c1 c2 pfc1) ≤ₛ smax (codeSize c1) (codeSize c2)

    oCast : ∀ {{æ : Æ}}
      → (csource cdest : ℂ ℓ)
      →  (x : El csource)
      → ( pfc1 : if¬Pos ⁇Allowed
        (smax (codeSize csource) (codeSize cdest)  ≡p size)
        (elSize csource x ≡p size))
      -> LÆ ( Σ[ xdest ∈ El cdest ]( elSize cdest xdest ≤ₛ elSize csource x ) )


open SizedCastMeet public

data Hide (a : Set) : Set where
  hide : ∀ {arg : a} → Hide a

reveal : ∀ {a} → Hide a → a
reveal (hide {arg = x}) = x



--If cSize is a codeSize, then cSize is not zero and we must not be in ⁇pos mode
-- codeNotZero : ∀ {ℓ} {c : ℂ ℓ} {⁇Allowed} {A : Set}
--   → {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p codeSize c}
--   → Hide (⁇Allowed ≡p ⁇pos → A)
-- codeNotZero {c = c} {posNoCode = posNoCode} = hide {arg = λ pf → Empty.elim (¬Z<↑ SZ (codeSuc c ≤⨟ pSubst (λ x → x ≤ₛ SZ) (posNoCode pf) ≤ₛ-refl))}

-- maxNotZero : ∀ {ℓ} {c1 c2 : ℂ ℓ} {⁇Allowed} {A : Set}
--   → {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p smax (codeSize c1) (codeSize c2)}
--   → Hide (⁇Allowed ≡p ⁇pos → A)
-- maxNotZero {c1 = c1} {c2 = c2} {posNoCode = posNoCode} = hide {arg = λ pf → Empty.elim (¬Z<↑ SZ (codeSuc c1 ≤⨟ smax-≤L ≤⨟ pSubst (λ x → x ≤ₛ SZ) (posNoCode pf) ≤ₛ-refl ))}


record SmallerCastMeet (⁇Allowed : ⁇Flag) (ℓ : ℕ) (size : Size) : Set where
  constructor smallerCastMeet
  field
    self : ∀ {allowed ℓ' s} → ∥ ( ℓ' , allowed , s) <CastComp ( ℓ , ⁇Allowed , size) ∥₁ → SizedCastMeet allowed ℓ' s
    ▹self : ∀ {⁇Allowed ℓ' s} → ▹Mod.▹ (SizedCastMeet ⁇Allowed ℓ' s)
  --useful helper
  <Size : ∀ {s} → (s <ₛ size) → ∥ ( ℓ , ⁇Allowed , s ) <CastComp ( ℓ , ⁇Allowed , size) ∥₁
  <Size lt = ∣ <LexR reflc (<LexR reflc lt) ∣₁

  notPosL' : ∀ (x : ⁇Flag)
        (np : notPos x)
        {A B : Set} → A → if¬Pos x A B
  notPosL' (Fin.zero) np a = a
  notPosL' (Fin.suc (Fin.suc Fin.zero)) np a = a

  notPosR' : ∀ (x : ⁇Flag)
    (np : x ≡p ⁇pos)
      {A B : Set} → B → if¬Pos x A B
  notPosR' x reflp b = b

  notPosIrrefut : ∀
    { np : notPos ⁇Allowed}
    {A B : Set} → A → (if¬Pos ⁇Allowed A B )
  notPosIrrefut {np = np} a = notPosL' _ np a

  isPosIrrefut : ∀
    {pos : ⁇Allowed ≡p ⁇pos}
    {A B : Set} → B → (if¬Pos ⁇Allowed A B )
  isPosIrrefut {pos = pos} b = notPosR' _ pos b

  argNotPos : ∀
    {@(tactic assumption) np : notPos ⁇Allowed}
    {A B : Set} → A → Hide (if¬Pos ⁇Allowed A B )
  argNotPos {np = np} a = hide {arg = notPosL' ⁇Allowed np a}

  argPos : ∀
    {@(tactic assumption) pos : ⁇Allowed ≡p ⁇pos}
    {A B : Set} → B → Hide (if¬Pos ⁇Allowed A B )
  argPos {pos = pos} b = hide {arg = notPosR' ⁇Allowed pos b}


    --
  infix 20 ⁇_By_
  ⁇_By_ : ∀ {{_ : Æ}}
      → {@(tactic assumption) np : notPos ⁇Allowed}
      → (c : ℂ ℓ) → (lt : Hide (codeSize c <ₛ size)) → (El c)
  ⁇_By_ {np = np} c (hide {lt}) = o⁇ (self (<Size lt)) np c reflp

  infix 20 [_]⁇_By_
  [_]⁇_By_ : ∀ (æ : Æ)
      → {@(tactic assumption) np : notPos ⁇Allowed}
      → (c : ℂ ℓ) → (lt : Hide (codeSize c <ₛ size)) → (El {{æ = æ}} c)
  [_]⁇_By_ æ  = ⁇_By_ {{æ}}

  infix 20 _∋_⊓_By_
  _∋_⊓_By_ : ∀ {{_ : Æ}}
      → (c : ℂ ℓ)
      → (x y : El c)
      → (ltc : Hide (if¬Pos ⁇Allowed
        (codeSize c <ₛ size)
        (smax (elSize c x) (elSize c y) <ₛ size)))
      → LÆ (El c)
  _∋_⊓_By_  c x y (hide {ltc})  with ⁇match ⁇Allowed
  ... | inl reflp = oMeet (self (<Size ltc)) c x y reflp
  ... | inr (inl reflp) = oMeet (self (<Size ltc)) c x y  reflp
  ... | inr (inr reflp) = oMeet (self (<Size ltc)) c x y reflp
      -- oMeet (self  (<Size lt)) c x y reflp

  infix 20 [_]_∋_⊓_By_
  [_]_∋_⊓_By_ : ∀ (æ : Æ)
      → (c : ℂ ℓ)
      → (x y : El {{æ = æ}} c)
      → (ltc : Hide (if¬Pos ⁇Allowed
        (codeSize c <ₛ size)
        (smax (elSize {{æ = æ}} c x) (elSize {{æ = æ}} c y) <ₛ size)))
      → LÆ {{æ = æ}} (El {{æ = æ}} c)
  [_]_∋_⊓_By_ æ = _∋_⊓_By_ {{æ}}


  infix 20 _⊓_By_
  _⊓_By_ :
      {@(tactic assumption) np : notPos ⁇Allowed}
      → (c1 c2 : ℂ ℓ)
      → (lt : Hide (smax (codeSize c1) (codeSize c2) <ₛ size))
      → (ℂ ℓ)
  _⊓_By_ {np} c1 c2 (hide {lt}) =
      oCodeMeet (self (<Size lt)) np c1 c2 reflp

  -- infix 20 _⊓⁇_By_
  -- _⊓⁇_By_ :
  --     {{_ : Æ}}
  --     (x1 x2 : ⁇Ty ℓ)
  --     → (cpf : S1 ≡p cSize)
  --     → (lt : Hide (smax (elSize C⁇ x1) (elSize C⁇ x2 ) <ₛ vSize))
  --     → LÆ (⁇Ty ℓ)
  -- _⊓⁇_By_  x1 x2 cpf (hide {lt}) = oMeet (self (<VSize (ptoc cpf) lt)) C⁇ x1 x2 {!!} reflp

  codeMeetEq : ∀
      {@(tactic assumption) np : notPos ⁇Allowed}
      → (c1 c2 : ℂ ℓ)
      → {lt1 lt2 : Hide (smax (codeSize c1) (codeSize c2) <ₛ size)}
      → ApproxEl (c1 ⊓ c2 By lt1) ≡ ApproxEl (c1 ⊓ c2 By lt2)
  codeMeetEq {np} c1 c2 {hide {arg = lt1}} {hide {arg = lt2}} = (cong (λ lt → ApproxEl (oCodeMeet (self lt) np c1 c2 reflp))) (squash₁ (<Size lt1) (<Size lt2))

  infix 20 _⊓Size_By_
  _⊓Size_By_ :
      {@(tactic assumption) np : notPos ⁇Allowed}
      → (c1 c2 : ℂ ℓ)
      → (lt : Hide (smax (codeSize c1) (codeSize c2) <ₛ size))
      →  codeSize (c1 ⊓ c2 By lt ) ≤ₛ smax (codeSize c1) (codeSize c2)
  _⊓Size_By_ {np} c1 c2 (hide {lt}) =
      oCodeMeetSize (self (<Size lt)) np c1 c2 reflp

  infix 20 ⟨_⇐_⟩_By_
  ⟨_⇐_⟩_By_ : ∀ {{_ : Æ}}
      → (cdest csource : ℂ ℓ)
      → (x : El csource)
      → (ltc : Hide (if¬Pos ⁇Allowed
             (smax (codeSize csource)  (codeSize cdest) <ₛ size)
             (elSize csource x <ₛ size)))
      → LÆ (El cdest)
  ⟨_⇐_⟩_By_ cdest csource x (hide {clt}) with ⁇match ⁇Allowed
  ... | inl reflp = fst <$> oCast (self (<Size clt)) csource cdest x reflp
  ... | inr (inl reflp) = fst <$> oCast (self (<Size clt)) csource cdest x reflp
  ... | inr (inr reflp) = fst <$> oCast (self (<Size clt)) csource cdest x reflp


  infix 20 [_]⟨_⇐_⟩_By_
  [_]⟨_⇐_⟩_By_ : ∀ (æ : Æ)
      → (cdest csource : ℂ ℓ)
      → (x : El {{æ = æ}} csource)
      → (ltc : Hide (if¬Pos ⁇Allowed
             (smax (codeSize csource)  (codeSize cdest) <ₛ size)
             (elSize {{æ = æ}} csource x <ₛ size)))
      → LÆ {{æ = æ}} (El {{æ = æ}} cdest)
  [_]⟨_⇐_⟩_By_ æ = ⟨_⇐_⟩_By_ {{æ}}


  -- Helper to manage the common case of having two elements of different codes' types,
  -- casting them to the meet code, then taking the meet of those two elements
  infix 20 _,,_∋_⊓_By_
  _,,_∋_⊓_By_ :
    ∀ {{æ : Æ}} →
    {@(tactic assumption) np : notPos ⁇Allowed} →
    ∀ c1 c2 →
      (x : El c1) →
      (y : El c2) →
      (clt : Hide (smax (codeSize c1) (codeSize c2) <ₛ size)) →
      -- (vlt : Hide (⁇Allowed ≡p ⁇pos → smax (elSize c1 x) (elSize c2 y) <ₛ vSize)) →
      {lt : _} →
      LÆ (El (c1 ⊓ c2 By (hide {arg = lt }) ))
  _,,_∋_⊓_By_ {np = np}  c1 c2 x1 x2 clt  {lt = lt} = do
   -- let lt = smax<-∞ (reveal lt∞)
   let c12 = (c1 ⊓ c2 By hide {arg = lt})
   let
     lt1 =
       ≤ₛ-sucMono
         (smax-monoR (c1 ⊓Size c2 By hide {arg = lt})
         ≤⨟ smax-assocL (codeSize c1) (codeSize c1) (codeSize c2)
         ≤⨟ smax-monoL smax-idem
         )
         ≤⨟ reveal clt
   let
     lt2 =
       ≤ₛ-sucMono (
         smax-monoR (c1 ⊓Size c2 By hide {arg = lt} ≤⨟ smax-commut _ _)
         ≤⨟ smax-assocL _ _ _
         ≤⨟ smax-commut _ _
         ≤⨟ smax-monoR smax-idem
         )
       ≤⨟ reveal clt
   let
     lt12 =
       ≤ₛ-sucMono (
         (c1 ⊓Size c2 By hide {arg = lt})
         -- ≤⨟ smax-mono (smax∞-self _) (smax∞-self _)
         )
       ≤⨟ reveal clt
   x1-12 ←  (⟨ c12 ⇐ c1 ⟩ x1
        By
          argNotPos lt1 --lt1
          -- hide {arg = λ pf → ≤< smax-≤L (reveal vlt pf) }
          )
   x2-12 ←  (⟨ c12 ⇐ c2 ⟩ x2
     By argNotPos lt2
     )
   c12 ∋ x1-12 ⊓ x2-12
     By
       argNotPos lt12


  [_]_,,_∋_⊓_By_ :
    ∀ (æ : Æ)
      {@(tactic assumption) np : notPos ⁇Allowed} →
      ∀ c1 c2 →
      (x : El {{æ = æ}} c1) →
      (y : El {{æ = æ}} c2) →
      (clt : Hide (smax ( codeSize c1) ( codeSize c2) <ₛ size)) →
      {lt : _} →
      LÆ {{æ = æ}} (El {{æ = æ}} (c1 ⊓ c2 By (hide {arg = lt }) ))
  [_]_,,_∋_⊓_By_ æ = _,,_∋_⊓_By_ {{æ = æ}}



  ⟨_,_⇐⊓⟩_By_ : ∀ {{æ : Æ}} c1 c2
    → {@(tactic assumption) np : notPos ⁇Allowed}
      {lt : _}
    → let c1⊓c2 = (c1 ⊓ c2 By (hide {arg = lt }) )
    in (x12 : El c1⊓c2)
    → (clt : Hide ( smax (codeSize c1)  (codeSize c2) <ₛ size))
    → LÆ (El c1 × El c2)
  ⟨_,_⇐⊓⟩_By_ c1 c2  {lt = lt} x clt  = do
    let c12 = c1 ⊓ c2 By hide {arg = lt}
    let
      lt1 =
        ≤ₛ-sucMono (
          smax-monoL (c1 ⊓Size c2 By hide )
          ≤⨟ smax-commut _ _
          ≤⨟ smax-assocL _ _ _
          ≤⨟ smax-monoL smax-idem
          )
        ≤⨟ reveal clt
    let
      lt2 =
        ≤ₛ-sucMono (
          smax-monoL (c1 ⊓Size c2 By hide )
          ≤⨟ smax-assocR _ _ _
          ≤⨟ smax-monoR smax-idem)
        ≤⨟ reveal clt
    x1 ← ⟨ c1 ⇐ c12 ⟩ x
      By argNotPos lt1
    x2 ←  ⟨ c2 ⇐ c12 ⟩ x
      By argNotPos lt2
    pure (x1 , x2)

  [_]⟨_,_⇐⊓⟩_By_ : ∀ (æ : Æ) c1 c2
    → {@(tactic assumption) np : notPos ⁇Allowed}
    → {lt : _}
    → let c1⊓c2 = (c1 ⊓ c2 By (hide {arg = lt }) )
    in (x12 : El {{æ = æ}} c1⊓c2)
    → (clt : Hide (smax (codeSize c1)  (codeSize c2) <ₛ size))
    → LÆ {{æ = æ}} (El {{æ = æ}} c1 × El {{æ = æ}} c2)
  [_]⟨_,_⇐⊓⟩_By_ æ =  ⟨_,_⇐⊓⟩_By_ {{æ = æ}}

  infix 20 ⟨_⇐_⟩ₛ_By_
  ⟨_⇐_⟩ₛ_By_ : ∀ {{_ : Æ}}
      → (cdest csource : ℂ ℓ)
      → (x : El csource)
      → (ltc : Hide (if¬Pos ⁇Allowed
             (smax (codeSize csource)  (codeSize cdest) <ₛ size)
             (elSize csource x <ₛ size)))
      → LÆ ( Σ[ xdest ∈ El cdest ]( elSize cdest xdest ≤ₛ elSize csource x ) )
  ⟨_⇐_⟩ₛ_By_ cdest csource x (hide {clt}) with ⁇match ⁇Allowed
  ... | inl reflp = oCast (self (<Size clt)) csource cdest x reflp
  ... | inr (inl reflp) = oCast (self (<Size clt)) csource cdest x reflp
  ... | inr (inr reflp) = oCast (self (<Size clt)) csource cdest x reflp

  self-1 : ∀ {s} {{ inst : 0< ℓ }} → SizedCastMeet ⁇any (predℕ ℓ) s
  self-1 {s = _} ⦃ suc< ⦄ = self ∣ <LexL Nat.≤-refl ∣₁
  Lself :  ∀  {æ al ℓ' s} → (æ ≡p Exact) → LÆ {{æ = æ}} (SizedCastMeet al ℓ' s)
  Lself reflp = Later {{Exact}} λ tic → pure ⦃ Exact ⦄ (▹self  tic)

FixCastMeet :
  (∀ {⁇Allowed  ℓ  size} → SmallerCastMeet ⁇Allowed ℓ size → SizedCastMeet ⁇Allowed ℓ size)
  → ∀ ⁇Allowed  ℓ  size → SizedCastMeet ⁇Allowed ℓ size
FixCastMeet f  =
  ▹Mod.fix λ ▹self →
    λ _ _ _ →
    WFI.induction CastCompWellFounded {P = λ {(ℓ' , a , s) → SizedCastMeet a ℓ' s}}
      (λ {(a , ℓ' , s) → λ self → f (smallerCastMeet (self ( _ , _ , _)) λ {a} {ℓ'} {s} → λ tic → ▹self tic a ℓ' s)}) _
