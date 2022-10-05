
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Sum
import Cubical.Data.Empty as Empty
-- open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Equality
open import Inductives
open import GuardedAlgebra
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude

open import ApproxExact
open import InductiveCodes
open import CodeSize
-- open import CodePair
open import WMuEq

module CastComp.Interface {{_ : DataTypes}} {{_ : DataGerms}} {{_ : InductiveCodes}}   where

open import Code
open import Head
open import Util
open import SizeOrd
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

  ifPos : ⁇Flag → Set → Set → Set
  ifPos Fin.zero A B = A
  ifPos (Fin.suc Fin.zero) A B = B
  ifPos (Fin.suc (Fin.suc Fin.zero)) A B = A

  notPos : ⁇Flag → Set
  notPos x = (x ≡p ⁇none) ⊎ (x ≡p ⁇any)

  depIfPos : ∀ {A B : Set} → (x : ⁇Flag) → (notPos x → A) → (x ≡p ⁇pos → B) → ifPos x A B
  depIfPos Fin.zero a b = a (inl reflp)
  depIfPos (Fin.suc Fin.zero) a b = b reflp
  depIfPos (Fin.suc (Fin.suc Fin.zero)) a b = a (inr reflp)


  isPropNotPos : ∀ {x} → isProp (notPos x)
  isPropNotPos {Fin.zero} (inl x) (inl x₁) = cong inl (isPropP Fin.isSetFin)
  isPropNotPos {Fin.suc x} (inr x₁) (inr x₂) = cong inr (isPropP Fin.isSetFin)


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
CastCompMeasure = ⁇Flag × ℕ × Size × Size

-- We can define the lexicographic-ordering on this measure
_<CastComp_ : (m1 m2 : CastCompMeasure) → Set
_<CastComp_ = _<Lex_ {_<a_ = _<Flag_} {_<b_ = _<Lex_ {_<a_ = Nat._<_} {_<b_ = _<Lex_ {_<a_ = _<ₛ_} {_<b_ = _<ₛ_}}}

CastCompWellFounded : WellFounded (λ x y → ∥ x <CastComp y ∥)
CastCompWellFounded = ∥LexWellFounded∥ ⁇FlagWellFounded (LexWellFounded Nat.<-wellfounded (LexWellFounded sizeWF sizeWF))

open import Germ
record SizedCastMeet (⁇Allowed : ⁇Flag) (ℓ : ℕ) (cSize vSize : Size) : Set where
  field

    o⁇ : ∀ {{æ : Æ}}
      → notPos ⁇Allowed
      → (c : ℂ ℓ)
      → (pfc1 : codeSize c ≡p cSize )
      → ( pfv2 : SZ ≡p vSize )
      → (El c)

    oMeet : ∀ {{æ : Æ}}
      → (c : ℂ ℓ)
      → (x y : El c)
      → ( pfc1 : ifPos ⁇Allowed
        ((codeSize c)  ≡p cSize)
        (SZ  ≡p cSize) )
      → ( pfv1 : smax (elSize c x) (elSize c y)  ≡p vSize )
      → LÆ (El c)
      -- → LÆ (Σ[ x⊓y ∈ El c ] (elSize c x⊓y ≤ₛ vSize))



    oCodeMeet :
      notPos ⁇Allowed
      → (c1 c2 : ℂ ℓ)
      → ( pfc1 : smax (codeSize c1) (codeSize c2)  ≡p cSize )
      → ( pfv1 : SZ  ≡p vSize )
      → (ℂ ℓ)

    oCodeMeetSize :
      (np : notPos ⁇Allowed)
      → (c1 c2 : ℂ ℓ)
      → ( pfc1 : smax (codeSize c1) (codeSize c2)  ≡p cSize )
      → ( pfv1 : SZ  ≡p vSize )
      → codeSize (oCodeMeet np c1 c2 pfc1 pfv1) ≤ₛ smax (codeSize c1) (codeSize c2)

    oCast : ∀ {{æ : Æ}}
      → (csource cdest : ℂ ℓ)
      → ( pfc1 : ifPos ⁇Allowed
        (smax (codeSize csource) (codeSize cdest)  ≡p cSize)
        (SZ  ≡p cSize))
      →  (x : El csource)
      → ( pfv1 : elSize csource x ≡p vSize)
      -> LÆ ( Σ[ xdest ∈ El cdest ]( elSize cdest xdest ≤ₛ elSize csource x ) )


open SizedCastMeet public

data Hide (a : Set) : Set where
  hide : ∀ {arg : a} → Hide a

reveal : ∀ {a} → Hide a → a
reveal (hide {arg = x}) = x



--If cSize is a codeSize, then cSize is not zero and we must not be in ⁇pos mode
codeNotZero : ∀ {ℓ} {c : ℂ ℓ} {⁇Allowed} {A : Set}
  → {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p codeSize c}
  → Hide (⁇Allowed ≡p ⁇pos → A)
codeNotZero {c = c} {posNoCode = posNoCode} = hide {arg = λ pf → Empty.elim (¬Z<↑ SZ (codeSuc c ≤⨟ pSubst (λ x → x ≤ₛ SZ) (posNoCode pf) ≤ₛ-refl))}

maxNotZero : ∀ {ℓ} {c1 c2 : ℂ ℓ} {⁇Allowed} {A : Set}
  → {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p smax (codeSize c1) (codeSize c2)}
  → Hide (⁇Allowed ≡p ⁇pos → A)
maxNotZero {c1 = c1} {c2 = c2} {posNoCode = posNoCode} = hide {arg = λ pf → Empty.elim (¬Z<↑ SZ (codeSuc c1 ≤⨟ smax-≤L ≤⨟ pSubst (λ x → x ≤ₛ SZ) (posNoCode pf) ≤ₛ-refl ))}


record SmallerCastMeet (⁇Allowed : ⁇Flag) (ℓ : ℕ) (cSize vSize : Size) : Set where
  constructor smallerCastMeet
  field
    self : ∀ {allowed ℓ' cs vs} → ∥ (allowed , ℓ' , cs , vs) <CastComp (⁇Allowed , ℓ , cSize , vSize) ∥ → SizedCastMeet allowed ℓ' cs vs
    ▹self : ∀ {⁇Allowed ℓ' cs vs} → ▹Mod.▹ (SizedCastMeet ⁇Allowed ℓ' cs vs)
  --useful helper
  <CSize : ∀ {cs vs} → (cs <ₛ cSize) → ∥ (⁇Allowed , ℓ , cs , vs) <CastComp (⁇Allowed , ℓ , cSize , vSize) ∥
  <CSize lt = ∣ <LexR reflc (<LexR reflc (<LexL lt)) ∣

  <VSize : ∀ {cs vs} → cs ≡ cSize → (vs <ₛ vSize) → ∥ (⁇Allowed , ℓ , cs , vs) <CastComp (⁇Allowed , ℓ , cSize , vSize) ∥
  <VSize ceq lt = ∣ <LexR reflc (<LexR reflc (<LexR ceq lt)) ∣



    --
  infix 20 ⁇_By_
  ⁇_By_ : ∀ {{_ : Æ}}
      → {@(tactic assumption) np : notPos ⁇Allowed}
      → (c : ℂ ℓ) → (lt : Hide (codeSize c <ₛ cSize)) → (El c)
  ⁇_By_ {np = np} c (hide {lt}) = o⁇ (self (<CSize lt)) np c reflp reflp

  infix 20 [_]⁇_By_
  [_]⁇_By_ : ∀ (æ : Æ)
      → {@(tactic assumption) np : notPos ⁇Allowed}
      → (c : ℂ ℓ) → (lt : Hide (codeSize c <ₛ cSize)) → (El {{æ = æ}} c)
  [_]⁇_By_ æ  = ⁇_By_ {{æ}}

  infix 20 _∋_⊓_cBy_vBy_
  _∋_⊓_cBy_vBy_ : ∀ {{_ : Æ}}
      → (c : ℂ ℓ)
      → {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p cSize}
      → (x y : El c)
      → (ltc : Hide (notPos ⁇Allowed → codeSize c <ₛ cSize))
      → (ltv : Hide (  ⁇Allowed ≡p ⁇pos → smax (elSize c x) (elSize c y) <ₛ vSize))
      → LÆ (El c)
  _∋_⊓_cBy_vBy_  c {posNoCode} x y (hide {ltc}) (hide {ltv}) with ⁇match ⁇Allowed
  ... | inl reflp = oMeet (self (<CSize (ltc (inr reflp)))) c x y reflp reflp
  ... | inr (inl reflp) = oMeet (self (<VSize reflc (ltv reflp))) c x y (posNoCode reflp) reflp
  ... | inr (inr reflp) = oMeet (self (<CSize (ltc (inl reflp)))) c x y reflp reflp
      -- oMeet (self  (<CSize lt)) c x y reflp reflp

  infix 20 [_]_∋_⊓_cBy_vBy_
  [_]_∋_⊓_cBy_vBy_ : ∀ (æ : Æ)
      → (c : ℂ ℓ)
      → {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p cSize}
      → (x y : El {{æ = æ}} c)
      → (lt : Hide (notPos ⁇Allowed → codeSize c <ₛ cSize))
      → (ltv : Hide ( ⁇Allowed ≡p ⁇pos → smax (elSize {{æ = æ}} c x) (elSize {{æ = æ}} c y) <ₛ vSize))
      → LÆ {{æ = æ}} (El {{æ = æ}} c)
  [_]_∋_⊓_cBy_vBy_ æ = _∋_⊓_cBy_vBy_ {{æ}}


  infix 20 _⊓_By_
  _⊓_By_ :
      {@(tactic assumption) np : notPos ⁇Allowed}
      → (c1 c2 : ℂ ℓ)
      → (lt : Hide (smax (codeSize c1) (codeSize c2) <ₛ cSize))
      → (ℂ ℓ)
  _⊓_By_ {np} c1 c2 (hide {lt}) =
      oCodeMeet (self (<CSize lt)) np c1 c2 reflp reflp

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
      → {lt1 lt2 : Hide (smax (codeSize c1) (codeSize c2) <ₛ cSize)}
      → ApproxEl (c1 ⊓ c2 By lt1) ≡ ApproxEl (c1 ⊓ c2 By lt2)
  codeMeetEq {np} c1 c2 {hide {arg = lt1}} {hide {arg = lt2}} = (cong (λ lt → ApproxEl (oCodeMeet (self lt) np c1 c2 reflp reflp))) (∥_∥.squash (<CSize lt1) (<CSize lt2))

  infix 20 _⊓Size_By_
  _⊓Size_By_ :
      {@(tactic assumption) np : notPos ⁇Allowed}
      → (c1 c2 : ℂ ℓ)
      → (lt : Hide (smax (codeSize c1) (codeSize c2) <ₛ cSize))
      →  codeSize (c1 ⊓ c2 By lt ) ≤ₛ smax (codeSize c1) (codeSize c2)
  _⊓Size_By_ {np} c1 c2 (hide {lt}) =
      oCodeMeetSize (self (<CSize lt)) np c1 c2 reflp reflp

  infix 20 ⟨_⇐_⟩_cBy_vBy_
  ⟨_⇐_⟩_cBy_vBy_ : ∀ {{_ : Æ}}
      → {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p cSize}
      → (cdest csource : ℂ ℓ)
      → (x : El csource)
      → (ltc : Hide (notPos ⁇Allowed → smax (codeSize csource)  (codeSize cdest) <ₛ cSize))
      → (ltv : Hide (  ⁇Allowed ≡p ⁇pos → elSize csource x <ₛ vSize))
      → LÆ ( Σ[ xdest ∈ El cdest ]( elSize cdest xdest ≤ₛ elSize csource x ) )
  ⟨_⇐_⟩_cBy_vBy_ {posNoCode} cdest csource x (hide {clt}) (hide {vlt}) with ⁇match ⁇Allowed
  ... | inl reflp = oCast (self (<CSize (clt (inr reflp)))) csource cdest reflp x reflp
  ... | inr (inl reflp) = oCast (self (<VSize reflc (vlt reflp))) csource cdest (posNoCode reflp) x reflp
  ... | inr (inr reflp) = oCast (self (<CSize (clt (inl reflp)))) csource cdest reflp x reflp
      -- oCast (self ((<CSize lt))) csource cdest reflp x reflp


  infix 20 [_]⟨_⇐_⟩_cBy_vBy_
  [_]⟨_⇐_⟩_cBy_vBy_ : ∀ (æ : Æ)
      → {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p cSize}
      → (cdest csource : ℂ ℓ)
      → (x : El {{æ = æ}} csource)
      → (ltc : Hide (notPos ⁇Allowed → smax (codeSize csource)  (codeSize cdest) <ₛ cSize))
      → (ltv : Hide (  ⁇Allowed ≡p ⁇pos → elSize {{æ = æ}} csource x <ₛ vSize))
      → LÆ {{æ = æ}} ( Σ[ xdest ∈ El {{æ = æ}} cdest ]( elSize {{æ = æ}} cdest xdest ≤ₛ elSize {{æ = æ}} csource x ) )
  [_]⟨_⇐_⟩_cBy_vBy_ æ = ⟨_⇐_⟩_cBy_vBy_ {{æ}}


  -- Helper to manage the common case of having two elements of different codes' types,
  -- casting them to the meet code, then taking the meet of those two elements
  infix 20 _,,_∋_⊓_By_
  _,,_∋_⊓_By_ :
    ∀ {{æ : Æ}} →
    {@(tactic assumption) np : notPos ⁇Allowed} →
    {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p cSize} →
    ∀ c1 c2 →
      (x : El c1) →
      (y : El c2) →
      (clt : Hide (smax (codeSize c1) (codeSize c2) <ₛ cSize)) →
      -- (vlt : Hide (⁇Allowed ≡p ⁇pos → smax (elSize c1 x) (elSize c2 y) <ₛ vSize)) →
      {lt : _} →
      LÆ (El (c1 ⊓ c2 By (hide {arg = lt }) ))
  _,,_∋_⊓_By_ {np = np} {posNoCode = pnc} c1 c2 x1 x2 clt  {lt = lt} = do
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
   (x1-12 , vlt1) ←  (⟨ c12 ⇐ c1 ⟩ x1
        cBy
          hide {arg = λ _ → lt1 } --lt1
        vBy hide {arg = λ pf → Empty.elim (¬Z<↑ _ (lt12 ≤⨟  pSubst (λ x → x ≤ₛ SZ) (pnc pf) ≤ₛ-Z)) }
          -- hide {arg = λ pf → ≤< smax-≤L (reveal vlt pf) }
          )
   (x2-12 , vlt2) ←  (⟨ c12 ⇐ c2 ⟩ x2
     cBy hide {arg = λ _ → lt2} --lt2
     vBy hide {arg = λ pf → Empty.elim (¬Z<↑ _ (lt12 ≤⨟  pSubst (λ x → x ≤ₛ SZ) (pnc pf) ≤ₛ-Z)) }
     )
   c12 ∋ x1-12 ⊓ x2-12
     cBy
       hide {arg = λ _ → lt12 }  -- lt12
     vBy hide {arg = λ pf → Empty.elim (¬Z<↑ _ (lt12 ≤⨟  pSubst (λ x → x ≤ₛ SZ) (pnc pf) ≤ₛ-Z)) }


  [_]_,,_∋_⊓_By_ :
    ∀ (æ : Æ)
      {@(tactic assumption) np : notPos ⁇Allowed} →
      {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p cSize} →
      ∀ c1 c2 →
      (x : El {{æ = æ}} c1) →
      (y : El {{æ = æ}} c2) →
      (clt : Hide (smax ( codeSize c1) ( codeSize c2) <ₛ cSize)) →
      {lt : _} →
      LÆ {{æ = æ}} (El {{æ = æ}} (c1 ⊓ c2 By (hide {arg = lt }) ))
  [_]_,,_∋_⊓_By_ æ = _,,_∋_⊓_By_ {{æ = æ}}



  ⟨_,_⇐⊓⟩_By_ : ∀ {{æ : Æ}} c1 c2
    → {@(tactic assumption) np : notPos ⁇Allowed}
    → {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p cSize}
      {lt : _}
    → let c1⊓c2 = (c1 ⊓ c2 By (hide {arg = lt }) )
    in (x12 : El c1⊓c2)
    → (clt : Hide ( smax (codeSize c1)  (codeSize c2) <ₛ cSize))
    → LÆ ((Σ[ x1 ∈ El c1 ] (elSize c1 x1 ≤ₛ elSize c1⊓c2 x12))
       × (Σ[ x2 ∈ El c2 ] (elSize c2 x2 ≤ₛ elSize c1⊓c2 x12)) )
  ⟨_,_⇐⊓⟩_By_ c1 c2 {posNoCode = pnc} {lt = lt} x clt  = do
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
      cBy hide {arg = λ _ →  lt1}
      vBy hide {arg = λ pf → Empty.elim (¬Z<↑ _ (lt1 ≤⨟  pSubst (λ x → x ≤ₛ SZ) (pnc pf) ≤ₛ-Z)) }
    x2 ←  ⟨ c2 ⇐ c12 ⟩ x
      cBy hide {arg =  λ _ → lt2}
      vBy hide {arg = λ pf → Empty.elim (¬Z<↑ _ (lt2 ≤⨟  pSubst (λ x → x ≤ₛ SZ) (pnc pf) ≤ₛ-Z)) }
    pure (x1 , x2)

  [_]⟨_,_⇐⊓⟩_By_ : ∀ (æ : Æ) c1 c2
    → {@(tactic assumption) np : notPos ⁇Allowed}
    → {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p cSize}
    → {lt : _}
    → let c1⊓c2 = (c1 ⊓ c2 By (hide {arg = lt }) )
    in (x12 : El {{æ = æ}} c1⊓c2)
    → (clt : Hide (smax (codeSize c1)  (codeSize c2) <ₛ cSize))
    → LÆ {{æ = æ}} ((Σ[ x1 ∈ El {{æ = æ}} c1 ] (elSize {{æ = æ}} c1 x1 ≤ₛ elSize {{æ = æ}} c1⊓c2 x12))
       × (Σ[ x2 ∈ El {{æ = æ}} c2 ] (elSize {{æ = æ}} c2 x2 ≤ₛ elSize {{æ = æ}} c1⊓c2 x12)) )
  [_]⟨_,_⇐⊓⟩_By_ æ =  ⟨_,_⇐⊓⟩_By_ {{æ = æ}}

  self-1 : ∀ {cs} {vs} {{ inst : 0< ℓ }} → SizedCastMeet ⁇Allowed (predℕ ℓ) cs vs
  self-1 {vs = _} ⦃ suc< ⦄ = self ∣ <LexR refl (<LexL Nat.≤-refl) ∣

FixCastMeet :
  (∀ {⁇Allowed  ℓ  cSize vSize} → SmallerCastMeet ⁇Allowed ℓ cSize vSize → SizedCastMeet ⁇Allowed ℓ cSize vSize)
  → ∀ ⁇Allowed  ℓ  cSize  vSize → SizedCastMeet ⁇Allowed ℓ cSize vSize
FixCastMeet f  =
  ▹Mod.fix λ ▹self →
    λ _ _ _ _ →
    WFI.induction CastCompWellFounded {P = λ {(a , ℓ' , cs , vs) → SizedCastMeet a ℓ' cs vs}}
      (λ {(a , ℓ' , cs , vs) → λ self → f (smallerCastMeet (self (_ , _ , _ , _)) λ {a} {ℓ'} {cs} {vs} → λ tic → ▹self tic a ℓ' cs vs)}) _
