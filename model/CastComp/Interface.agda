
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
-- open Ord ℂ El ℧ C𝟙 refl
open import Cubical.Data.FinData.Properties as Fin
import Cubical.Data.Nat.Order as Nat

import GuardedModality as ▹Mod
open import Cubical.Data.Sum

open import Assumption



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
CastCompMeasure = ℕ × Size × Size

-- We can define the lexicographic-ordering on this measure
_<CastComp_ : (m1 m2 : CastCompMeasure) → Set
_<CastComp_ = _<Lex_ {_<a_ = Nat._<_} {_<b_ = _<Lex_ {_<a_ = _<ₛ_}  {_<b_ = _<ₛ_}}

CastCompWellFounded : WellFounded (λ x y → ∥ x <CastComp y ∥₁)
CastCompWellFounded = ∥LexWellFounded∥ Nat.<-wellfounded (LexWellFounded sizeWF sizeWF)

open import Germ
record SizedCastMeet (ℓ : ℕ) (csize vsize : Size) : Set where
  field

    o⁇ : ∀ {{æ : Æ}}
      → (c : ℂ ℓ)
      → (pfc1 : codeSize c ≡p csize )
      → (El c)

    oMeet : ∀ {{æ : Æ}}
      → (c : ℂ ℓ)
      → (x y : El c)
      → ( pfc : (codeSize c)  ≡p csize)
      → LÆ (El c)

    -- oDataGermMeet : ∀ {{æ : Æ}} {tyCtor}
    --   → (x y : ⁇GermTy ℓ tyCtor)
    --   → smax (GermSize x) (GermSize y) ≡p size
    --   → LÆ (⁇GermTy ℓ tyCtor)


    oCodeMeet :
      (c1 c2 : ℂ ℓ)
      → ( pfc1 : smax (codeSize c1) (codeSize c2)  ≡p csize )
      → (ℂ ℓ)

    oCodeMeetSize :
      (c1 c2 : ℂ ℓ)
      → ( pfc1 : smax (codeSize c1) (codeSize c2)  ≡p csize )
      → codeSize (oCodeMeet c1 c2 pfc1) ≤ₛ smax (codeSize c1) (codeSize c2)

    oCast : ∀ {{æ : Æ}}
      → (csource cdest : ℂ ℓ)
      →  (x : El csource)
      → ( pfc1 : (smax (codeSize csource) (codeSize cdest)  ≡p csize))
      -> LÆ ( Σ[ xdest ∈ El cdest ]( elSize cdest xdest ≤ₛ elSize csource x ) )


open SizedCastMeet public

data Hide (a : Set) : Set where
  hide : ∀ {arg : a} → Hide a

reveal : ∀ {a} → Hide a → a
reveal (hide {arg = x}) = x


Decreasing_ : ∀ {a : Set} → a → Hide a
Decreasing_ x = hide {arg = x}

infixr 99 Decreasing_

--If cSize is a codeSize, then cSize is not zero and we must not be in ⁇pos mode
-- codeNotZero : ∀ {ℓ} {c : ℂ ℓ} {⁇Allowed} {A : Set}
--   → {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p codeSize c}
--   → Hide (⁇Allowed ≡p ⁇pos → A)
-- codeNotZero {c = c} {posNoCode = posNoCode} = hide {arg = λ pf → Empty.elim (¬Z<↑ SZ (codeSuc c ≤⨟ pSubst (λ x → x ≤ₛ SZ) (posNoCode pf) ≤ₛ-refl))}

-- maxNotZero : ∀ {ℓ} {c1 c2 : ℂ ℓ} {⁇Allowed} {A : Set}
--   → {@(tactic assumption) posNoCode : ⁇Allowed ≡p ⁇pos → SZ ≡p smax (codeSize c1) (codeSize c2)}
--   → Hide (⁇Allowed ≡p ⁇pos → A)
-- maxNotZero {c1 = c1} {c2 = c2} {posNoCode = posNoCode} = hide {arg = λ pf → Empty.elim (¬Z<↑ SZ (codeSuc c1 ≤⨟ smax-≤L ≤⨟ pSubst (λ x → x ≤ₛ SZ) (posNoCode pf) ≤ₛ-refl ))}


record SmallerCastMeet (ℓ : ℕ) (csize vsize : Size) : Set where
  constructor smallerCastMeet
  field
    self : ∀ {ℓ' cs vs} → ∥ ( ℓ' , cs , vs) <CastComp ( ℓ , csize , vsize) ∥₁ → SizedCastMeet ℓ' cs vs
    ▹self : ∀ {ℓ' cs vs} → ▹Mod.▹ (SizedCastMeet ℓ' cs vs)
  --useful helper
  <cSize : ∀ {cs} → (cs <ₛ csize) → ∥ ( ℓ , cs , SZ ) <CastComp ( ℓ , csize , vsize) ∥₁
  <cSize lt = ∣ <LexR reflc (<LexL lt) ∣₁
  <vSize : ∀ {vs} → (vs <ₛ vsize) → ∥ ( ℓ , csize , vs ) <CastComp ( ℓ , csize , vsize) ∥₁
  <vSize lt = ∣ <LexR reflc (<LexR reflc lt) ∣₁

  infix 20 ⁇_By_
  ⁇_By_ : ∀ {{_ : Æ}}
      → (c : ℂ ℓ) → (lt : Hide (codeSize c <ₛ csize)) → (El c)
  ⁇_By_  c (hide {lt}) = o⁇ (self (<cSize lt)) c reflp

  infix 20 [_]⁇_By_
  [_]⁇_By_ : ∀ (æ : Æ)
      → (c : ℂ ℓ) → (lt : Hide (codeSize c <ₛ csize)) → (El {{æ = æ}} c)
  [_]⁇_By_ æ  = ⁇_By_ {{æ}}

  infix 20 _∋_⊓_By_
  _∋_⊓_By_ : ∀ {{_ : Æ}}
      → (c : ℂ ℓ)
      → (x y : El c)
      → (Hide (codeSize c <ₛ csize))
      → LÆ (El c)
  _∋_⊓_By_  c x y (hide {ltc}) = oMeet (self (<cSize ltc)) c x y reflp
  -- with ⁇match ⁇Allowed
  -- ... | inl reflp = oMeet (self (<Size ltc)) c x y reflp
  -- ... | inr (inl reflp) = oMeet (self (<Size ltc)) c x y  reflp
  -- ... | inr (inr reflp) = oMeet (self (<Size ltc)) c x y reflp
  --     -- oMeet (self  (<Size lt)) c x y reflp

  infix 20 [_]_∋_⊓_By_
  [_]_∋_⊓_By_ : ∀ (æ : Æ)
      → (c : ℂ ℓ)
      → (x y : El {{æ = æ}} c)
      →  (Hide( codeSize c <ₛ csize))
      → LÆ {{æ = æ}} (El {{æ = æ}} c)
  [_]_∋_⊓_By_ æ = _∋_⊓_By_ {{æ}}


  infix 20 _⊓_By_
  _⊓_By_ :
      (c1 c2 : ℂ ℓ)
      → (lt : Hide (smax (codeSize c1) (codeSize c2) <ₛ csize))
      → (ℂ ℓ)
  _⊓_By_  c1 c2 (hide {lt}) =
      oCodeMeet (self (<cSize lt)) c1 c2 reflp

  -- infix 20 _⊓⁇_By_
  -- _⊓⁇_By_ :
  --     {{_ : Æ}}
  --     (x1 x2 : ⁇Ty ℓ)
  --     → (cpf : S1 ≡p cSize)
  --     → (lt : Hide (smax (elSize C⁇ x1) (elSize C⁇ x2 ) <ₛ vSize))
  --     → LÆ (⁇Ty ℓ)
  -- _⊓⁇_By_  x1 x2 cpf (hide {lt}) = oMeet (self (<VSize (ptoc cpf) lt)) C⁇ x1 x2 {!!} reflp

  codeMeetEq : ∀
      (c1 c2 : ℂ ℓ)
      → {lt1 lt2 : Hide (smax (codeSize c1) (codeSize c2) <ₛ csize)}
      → ApproxEl (c1 ⊓ c2 By lt1) ≡ ApproxEl (c1 ⊓ c2 By lt2)
  codeMeetEq  c1 c2 {hide {arg = lt1}} {hide {arg = lt2}} = (cong (λ lt → ApproxEl (oCodeMeet (self lt) c1 c2 reflp))) (squash₁ (<cSize lt1) (<cSize lt2))

  infix 20 _⊓Size_By_
  _⊓Size_By_ :
      (c1 c2 : ℂ ℓ)
      → (lt : Hide (smax (codeSize c1) (codeSize c2) <ₛ csize))
      →  codeSize (c1 ⊓ c2 By lt ) ≤ₛ smax (codeSize c1) (codeSize c2)
  _⊓Size_By_ c1 c2 (hide {lt}) =
      oCodeMeetSize (self (<cSize lt)) c1 c2 reflp

  infix 20 ⟨_⇐_⟩_By_
  ⟨_⇐_⟩_By_ : ∀ {{_ : Æ}}
      → (cdest csource : ℂ ℓ)
      → (x : El csource)
       → (Hide (smax (codeSize csource)  (codeSize cdest) <ₛ csize))
      → LÆ (El cdest)
  ⟨_⇐_⟩_By_ cdest csource x (hide {clt})
    = fst <$> oCast (self (<cSize clt)) csource cdest x reflp


  infix 20 [_]⟨_⇐_⟩_By_
  [_]⟨_⇐_⟩_By_ : ∀ (æ : Æ)
      → (cdest csource : ℂ ℓ)
      → (x : El {{æ = æ}} csource)
      →     Hide  (smax (codeSize csource)  (codeSize cdest) <ₛ csize)
      → LÆ {{æ = æ}} (El {{æ = æ}} cdest)
  [_]⟨_⇐_⟩_By_ æ = ⟨_⇐_⟩_By_ {{æ}}


  -- Helper to manage the common case of having two elements of different codes' types,
  -- casting them to the meet code, then taking the meet of those two elements
  infix 20 _,,_∋_⊓_By_
  _,,_∋_⊓_By_ :
    ∀ {{æ : Æ}} →
    ∀ c1 c2 →
      (x : El c1) →
      (y : El c2) →
      (clt : Hide (smax (codeSize c1) (codeSize c2) <ₛ csize)) →
      -- (vlt : Hide (⁇Allowed ≡p ⁇pos → smax (elSize c1 x) (elSize c2 y) <ₛ vSize)) →
      {lt : _} →
      LÆ (El (c1 ⊓ c2 By (hide {arg = lt }) ))
  _,,_∋_⊓_By_  c1 c2 x1 x2 clt  {lt = lt} = do
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
          Decreasing lt1
          -- hide {arg = λ pf → ≤< smax-≤L (reveal vlt pf) }
          )
   x2-12 ←  (⟨ c12 ⇐ c2 ⟩ x2
     By Decreasing lt2
     )
   c12 ∋ x1-12 ⊓ x2-12
     By Decreasing lt12


  [_]_,,_∋_⊓_By_ :
    ∀ (æ : Æ)
      c1 c2 →
      (x : El {{æ = æ}} c1) →
      (y : El {{æ = æ}} c2) →
      (clt : Hide (smax ( codeSize c1) ( codeSize c2) <ₛ csize)) →
      {lt : _} →
      LÆ {{æ = æ}} (El {{æ = æ}} (c1 ⊓ c2 By (hide {arg = lt }) ))
  [_]_,,_∋_⊓_By_ æ = _,,_∋_⊓_By_ {{æ = æ}}



  ⟨_,_⇐⊓⟩_By_ : ∀ {{æ : Æ}} c1 c2
      {lt : _}
    → let c1⊓c2 = (c1 ⊓ c2 By (hide {arg = lt }) )
    in (x12 : El c1⊓c2)
    → (clt : Hide ( smax (codeSize c1)  (codeSize c2) <ₛ csize))
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
      By Decreasing lt1
    x2 ←  ⟨ c2 ⇐ c12 ⟩ x
      By Decreasing lt2
    pure (x1 , x2)

  [_]⟨_,_⇐⊓⟩_By_ : ∀ (æ : Æ) c1 c2
    → {lt : _}
    → let c1⊓c2 = (c1 ⊓ c2 By (hide {arg = lt }) )
    in (x12 : El {{æ = æ}} c1⊓c2)
    → (clt : Hide (smax (codeSize c1)  (codeSize c2) <ₛ csize))
    → LÆ {{æ = æ}} (El {{æ = æ}} c1 × El {{æ = æ}} c2)
  [_]⟨_,_⇐⊓⟩_By_ æ =  ⟨_,_⇐⊓⟩_By_ {{æ = æ}}

  infix 20 ⟨_⇐_⟩ₛ_By_
  ⟨_⇐_⟩ₛ_By_ : ∀ {{_ : Æ}}
      → (cdest csource : ℂ ℓ)
      → (x : El csource)
      →  Hide (smax (codeSize csource)  (codeSize cdest) <ₛ csize)
      → LÆ ( Σ[ xdest ∈ El cdest ]( elSize cdest xdest ≤ₛ elSize csource x ) )
  ⟨_⇐_⟩ₛ_By_ cdest csource x (hide {clt}) = oCast (self (<cSize clt)) csource cdest x reflp

  self-1 : ∀ {cs vs} {{ inst : 0< ℓ }} → SizedCastMeet (predℕ ℓ) cs vs
  self-1 ⦃ suc< ⦄ = self ∣ <LexL Nat.≤-refl ∣₁
  Lself :  ∀  {æ ℓ' cs vs} → (æ ≡p Exact) → LÆ {{æ = æ}} (SizedCastMeet ℓ' cs vs)
  Lself reflp = Later {{Exact}} λ tic → pure ⦃ Exact ⦄ (▹self  tic)

FixCastMeet :
  (∀ { ℓ  csize vsize} → SmallerCastMeet ℓ csize vsize → SizedCastMeet ℓ csize vsize)
  → ∀ ℓ csize vsize → SizedCastMeet ℓ csize vsize
FixCastMeet f  =
  ▹Mod.fix λ ▹self →
    λ _ _ _ →
    WFI.induction CastCompWellFounded {P = λ {(ℓ' , cs , vs) → SizedCastMeet ℓ' cs vs}}
      (λ {(ℓ' , cs , vs) → λ self → f (smallerCastMeet (self ( _ , _ , _)) λ {ℓ'} {cs} {vs} → λ tic → ▹self tic ℓ' cs vs)}) _
