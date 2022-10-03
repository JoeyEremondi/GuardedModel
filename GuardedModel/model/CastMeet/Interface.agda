
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Bool
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

module CastMeet.Interface {{_ : DataTypes}} {{_ : DataGerms}} {{_ : InductiveCodes}}   where

open import Code
open import Head
open import Util
open import SizeOrd
open import WellFounded
-- open Ord ℂ El ℧ C𝟙 refl
open import Cubical.Data.Fin.Properties as Fin
import Cubical.Data.Nat.Order as Nat
open import Cubical.Data.Bool as Bool

import GuardedModality as ▹Mod


data CVMode : Set where
  CMode VMode : CVMode

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
CastCompMeasure = Bool × ℕ × Size × Size

-- We can define the lexicographic-ordering on this measure
_<CastComp_ : (m1 m2 : CastCompMeasure) → Set
_<CastComp_ = _<Lex_ {_<a_ = BoolOrder} {_<b_ = _<Lex_ {_<a_ = Nat._<_} {_<b_ = _<Lex_ {_<a_ = _<ₛ_} {_<b_ = _<ₛ_}}}

CastCompWellFounded : WellFounded (λ x y → ∥ x <CastComp y ∥)
CastCompWellFounded = ∥LexWellFounded∥ BoolWellFounded (LexWellFounded Nat.<-wellfounded (LexWellFounded sizeWF sizeWF))

record SizedCodeMeet (⁇Allowed : Bool) (ℓ : ℕ) (cSize : Size) : Set where
    o⁇ : ∀ {{æ : Æ}}  → (c : ℂ ℓ)
      → (pfc1 : codeSize c ≡p cSize )
      → (El c)


    oCodeMeet : ∀ {{æ : Æ}}
      → (c1 c2 : ℂ ℓ)
      → ( pfc1 : smax (codeSize c1) (codeSize c2)  ≡p cSize )
      → ℂ ℓ
open import Germ

record SizedCastMeet (⁇Allowed : Bool) (ℓ : ℕ) (cSize vSize : Size) : Set where
  field

    scm : SizedCodeMeet ⁇Allowed ℓ cSize

    -- The type returned in the first element of the Sigma should be equal to oCodeMeet
    -- but we can't write that property within the record itself, since they're at different value sizes
    -- TODO is this right?
    oMeetAt : ∀ {{æ : Æ}}
      → (c1 c2 : ℂ ℓ)
      → (x : El c1)
      → (y : El c2)
      → (cvm : CVMode)
      → ( pfc1 : cvm ≡p CMode → smax (codeSize c1) (codeSize c2)  ≡p cSize )
      → ( pfc2 : cvm ≡p VMode → cSize ≡p SZ )
      → ( pfc3 : cvm ≡p VMode → ⁇Allowed ≡p true )
      → ( pfv1 : smax (elSize c1 x) (elSize c2 y)  ≤ₛ vSize )
      → LÆ (El (oCodeMeet {!pfc1!} {!!} {!!}))

--   -- Source = cdest ⊓ cfactor
--   -- i.e. since it's an upcast, we know we're losing precision
--   -- so we can factor the source into the meet of the destination and some other type
--   -- in practice, this will be the source itself, since if source ⊑ dest, source ⊓ dest = dest
--   -- but again, we can't prove that until we've proerly defined precision
--   field
--     oUpCast : ∀ {{æ : Æ}}
--       → (cfactor cdest : ℂ ℓ)
--       → (cvm : CVMode)
--       → ( pfc1 : cvm ≡p CMode → smax (codeSize cfactor) (codeSize cdest)  ≡p cSize )
--       → ( pfc2 : cvm ≡p VMode → cSize ≡p SZ )
--       → ( pfc3 : cvm ≡p VMode → ⁇Allowed ≡p true )
--       → (pfv℧ : smax (elSize cfactor (℧ cfactor)) (elSize cdest (℧ cdest)) ≤ₛ vSize)
--       →  (x : El (fst (oMeetAt cfactor cdest (℧ cfactor) (℧ cdest) cvm pfc1 pfc2 pfc3 pfv℧)))
--       → ( pfv1 :  (elSize {!!} x)   ≡p vSize )
--       -> LÆ ( El cdest)


-- open SizedCastMeet public

-- data Hide (a : Set) : Set where
--   hide : ∀ {arg : a} → Hide a

-- reveal : ∀ {a} → Hide a → a
-- reveal (hide {arg = x}) = x







-- -- record SmallerCastMeet (⁇Allowed : Bool) (ℓ : ℕ) (cSize vSize : Size) : Set where
-- --   constructor smallerCastMeet
-- --   field
-- --     self : ∀ {allowed ℓ' cs vs} → ∥ (allowed , ℓ' , cs , vs) <CastComp (⁇Allowed , ℓ , cSize , vSize) ∥ → SizedCastMeet allowed ℓ' cs vs
-- --     ▹self : ∀ {⁇Allowed ℓ' cs vs} → ▹Mod.▹ (SizedCastMeet ⁇Allowed ℓ' cs vs)
-- --   --useful helper
-- --   <CSize : ∀ {cs vs} → (cs <ₛ cSize) → ∥ (⁇Allowed , ℓ , cs , vs) <CastComp (⁇Allowed , ℓ , cSize , vSize) ∥
-- --   <CSize lt = ∣ <LexR reflc (<LexR reflc (<LexL lt)) ∣

-- --   <VSize : ∀ {cs vs} → cs ≡ cSize → (vs <ₛ vSize) → ∥ (⁇Allowed , ℓ , cs , vs) <CastComp (⁇Allowed , ℓ , cSize , vSize) ∥
-- --   <VSize ceq lt = ∣ <LexR reflc (<LexR reflc (<LexR ceq lt)) ∣
-- --     --
-- --   infix 20 ⁇_By_
-- --   ⁇_By_ : ∀ {{_ : Æ}}
-- --       → (c : ℂ ℓ) → (lt : Hide (codeSize c <ₛ cSize)) → (El c)
-- --   ⁇_By_ c (hide {lt}) = o⁇ (self (<CSize lt)) c reflp reflp

-- --   infix 20 [_]⁇_By_
-- --   [_]⁇_By_ : ∀ (æ : Æ)
-- --       → (c : ℂ ℓ) → (lt : Hide (codeSize c <ₛ cSize)) → (El {{æ = æ}} c)
-- --   [_]⁇_By_ æ  = ⁇_By_ {{æ}}

-- --   infix 20 _∋_⊓_By_
-- --   _∋_⊓_By_ : ∀ {{_ : Æ}}
-- --       → (c : ℂ ℓ)
-- --       → (x y : El c)
-- --       → (lt : Hide (codeSize c <ₛ cSize))
-- --       → LÆ (El c)
-- --   _∋_⊓_By_   c x y (hide {lt}) =
-- --       oMeet (self  (<CSize lt)) c x y reflp reflp

-- --   infix 20 [_]_∋_⊓_By_
-- --   [_]_∋_⊓_By_ : ∀ (æ : Æ)
-- --       → (c : ℂ ℓ)
-- --       → (x y : El {{æ = æ}} c)
-- --       → (lt : Hide (codeSize c <ₛ cSize))
-- --       → LÆ {{æ = æ}} (El {{æ = æ}} c)
-- --   [_]_∋_⊓_By_ æ = _∋_⊓_By_ {{æ}}


-- --   infix 20 _⊓_By_
-- --   _⊓_By_ :
-- --       (c1 c2 : ℂ ℓ)
-- --       → (lt : Hide (smax (codeSize c1) (codeSize c2) <ₛ cSize))
-- --       → (ℂ ℓ)
-- --   _⊓_By_  c1 c2 (hide {lt}) =
-- --       oCodeMeet {vSize = SZ} (self (<CSize lt) ) c1 c2 reflp

-- --   infix 20 _⊓⁇_By_
-- --   _⊓⁇_By_ :
-- --       {{_ : Æ}}
-- --       (x1 x2 : ⁇Ty ℓ)
-- --       → (cpf : S1 ≡p cSize)
-- --       → (lt : Hide (smax (elSize C⁇ x1) (elSize C⁇ x2 ) <ₛ vSize))
-- --       → LÆ (⁇Ty ℓ)
-- --   _⊓⁇_By_  x1 x2 cpf (hide {lt}) =
-- --       oMeet (self (<VSize (ptoc cpf) lt)) C⁇ x1 x2 reflp reflp

-- --   codeMeetEq : ∀
-- --       (c1 c2 : ℂ ℓ)
-- --       → {lt1 lt2 : Hide (smax (codeSize c1) (codeSize c2) <ₛ cSize)}
-- --       → ApproxEl (c1 ⊓ c2 By lt1) ≡ ApproxEl (c1 ⊓ c2 By lt2)
-- --   codeMeetEq c1 c2 {hide {arg = lt1}} {hide {arg = lt2}} = (cong (λ lt → ApproxEl (oCodeMeet (self lt) c1 c2 reflp ))) (∥_∥.squash (<CSize lt1) (<CSize lt2))

-- --   infix 20 _⊓Size_By_
-- --   _⊓Size_By_ :
-- --       (c1 c2 : ℂ ℓ)
-- --       → (lt : Hide (smax (codeSize c1) (codeSize c2) <ₛ cSize))
-- --       →  codeSize (c1 ⊓ c2 By lt ) ≤ₛ smax (codeSize c1) (codeSize c2)
-- --   _⊓Size_By_  c1 c2 (hide {lt}) =
-- --       oCodeMeetSize (self (<CSize lt)) c1 c2 reflp

-- --   infix 20 ⟨_⇐_⟩_By_
-- --   ⟨_⇐_⟩_By_ : ∀ {{_ : Æ}}
-- --       → (cdest csource : ℂ ℓ)
-- --       → (x : El csource)
-- --       → (lt : Hide (smax (codeSize csource)  (codeSize cdest) <ₛ cSize))
-- --       → LÆ (El cdest)
-- --   ⟨_⇐_⟩_By_ cdest csource x (hide {lt}) =
-- --       oCast (self ((<CSize lt))) csource cdest reflp x reflp

-- --   +⟨_⇐_⟩_By_ : ∀ {{_ : Æ}}
-- --       → (cdest csource : ℂ ℓ)
-- --       → (x : El csource)
-- --       → (lt : Hide (elSize csource x <ₛ vSize))
-- --       → {@(tactic default (reflp {x = S1})) pf : cSize ≡p S1}
-- --       → LÆ (El cdest)
-- --   +⟨_⇐_⟩_By_ cdest csource x (hide {lt}) {pf = pf} =
-- --       oCast+ (self ((<VSize (sym (ptoc pf)) lt))) csource cdest reflp x reflp

-- --   infix 20 [_]⟨_⇐_⟩_By_
-- --   [_]⟨_⇐_⟩_By_ : ∀ (æ : Æ)
-- --       → (cdest csource : ℂ ℓ)
-- --       → (x : El {{æ = æ}} csource)
-- --       → (lt : Hide (smax (codeSize csource)  (codeSize cdest) <ₛ cSize))
-- --       → LÆ {{æ = æ}} (El {{æ = æ}} cdest)
-- --   [_]⟨_⇐_⟩_By_ æ = ⟨_⇐_⟩_By_ {{æ}}


-- --   -- Helper to manage the common case of having two elements of different codes' types,
-- --   -- casting them to the meet code, then taking the meet of those two elements
-- --   infix 20 _,,_∋_⊓_By_
-- --   _,,_∋_⊓_By_ :
-- --     ∀ {{æ : Æ}} c1 c2 →
-- --       (El c1) →
-- --       (El c2) →
-- --       (lt∞ : Hide (smax (codeSize c1) (codeSize c2) <ₛ cSize)) →
-- --       {lt : _} →
-- --       LÆ (El (c1 ⊓ c2 By (hide {arg = lt }) ) )
-- --   _,,_∋_⊓_By_ c1 c2 x1 x2 lt∞ {lt = lt} = do
-- --    -- let lt = smax<-∞ (reveal lt∞)
-- --    let c12 = (c1 ⊓ c2 By hide {arg = lt})
-- --    let
-- --      lt1 =
-- --        ≤ₛ-sucMono
-- --          (smax-monoR (c1 ⊓Size c2 By hide {arg = lt})
-- --          ≤⨟ smax-assocL (codeSize c1) (codeSize c1) (codeSize c2)
-- --          ≤⨟ smax-monoL smax-idem
-- --          )
-- --          ≤⨟ reveal lt∞
-- --    let
-- --      lt2 =
-- --        ≤ₛ-sucMono (
-- --          smax-monoR (c1 ⊓Size c2 By hide {arg = lt} ≤⨟ smax-commut _ _)
-- --          ≤⨟ smax-assocL _ _ _
-- --          ≤⨟ smax-commut _ _
-- --          ≤⨟ smax-monoR smax-idem
-- --          )
-- --        ≤⨟ reveal lt∞
-- --    let
-- --      lt12 =
-- --        ≤ₛ-sucMono (
-- --          (c1 ⊓Size c2 By hide {arg = lt})
-- --          -- ≤⨟ smax-mono (smax∞-self _) (smax∞-self _)
-- --          )
-- --        ≤⨟ reveal lt∞
-- --    x1-12 ←  (⟨ c12 ⇐ c1 ⟩ x1 By
-- --         hide {arg = lt1 })
-- --    x2-12 ←  (⟨ c12 ⇐ c2 ⟩ x2 By hide {arg = lt2})
-- --    c12 ∋ x1-12 ⊓ x2-12 By hide {arg = lt12 }


-- --   [_]_,,_∋_⊓_By_ :
-- --     ∀ (æ : Æ) c1 c2 →
-- --       (El {{æ = æ}} c1) →
-- --       (El {{æ = æ}} c2) →
-- --       (lt∞ : Hide (smax ( codeSize c1) ( codeSize c2) <ₛ cSize)) →
-- --       {lt : _} →
-- --       LÆ {{æ = æ}} (El {{æ = æ}} (c1 ⊓ c2 By hide {arg = lt}))
-- --   [_]_,,_∋_⊓_By_ æ = _,,_∋_⊓_By_ {{æ = æ}}

-- --   ⟨_,_⇐⊓⟩_By_ : ∀ {{æ : Æ}} c1 c2
-- --       {lt : _}
-- --     → El (c1 ⊓ c2 By (hide {arg = lt }) )
-- --     → (lt∞ : Hide (smax (codeSize c1)  (codeSize c2) <ₛ cSize))
-- --     → LÆ (El c1 × El c2)
-- --   ⟨_,_⇐⊓⟩_By_ c1 c2 {lt = lt} x lt∞  = do
-- --     let c12 = c1 ⊓ c2 By hide {arg = lt}
-- --     let
-- --       lt1 =
-- --         ≤ₛ-sucMono (
-- --           smax-monoL (c1 ⊓Size c2 By hide )
-- --           ≤⨟ smax-commut _ _
-- --           ≤⨟ smax-assocL _ _ _
-- --           ≤⨟ smax-monoL smax-idem
-- --           )
-- --         ≤⨟ reveal lt∞
-- --     let
-- --       lt2 =
-- --         ≤ₛ-sucMono (
-- --           smax-monoL (c1 ⊓Size c2 By hide )
-- --           ≤⨟ smax-assocR _ _ _
-- --           ≤⨟ smax-monoR smax-idem)
-- --         ≤⨟ reveal lt∞
-- --     x1 ← ⟨ c1 ⇐ c12 ⟩ x By hide {arg = lt1}
-- --     x2 ←  ⟨ c2 ⇐ c12 ⟩ x By hide {arg = lt2}
-- --     pure (x1 , x2)

-- --   [_]⟨_,_⇐⊓⟩_By_ : ∀ (æ : Æ) c1 c2
-- --       {lt : _}
-- --     → El {{æ = æ}} (c1 ⊓ c2 By (hide {arg = lt }) )
-- --     → (lt∞ : Hide (smax ( (codeSize c1)) ( (codeSize c2)) <ₛ cSize))
-- --     → LÆ {{æ = æ}} (El {{æ = æ}} c1 × El {{æ = æ}} c2)
-- --   [_]⟨_,_⇐⊓⟩_By_ æ =  ⟨_,_⇐⊓⟩_By_ {{æ = æ}}

-- --   self-1 : ∀ {cs} {vs} {{ inst : 0< ℓ }} → SizedCastMeet ⁇Allowed (predℕ ℓ) cs vs
-- --   self-1 {vs = _} ⦃ suc< ⦄ = self ∣ <LexR refl (<LexL Nat.≤-refl) ∣

-- -- FixCastMeet :
-- --   (∀ {⁇Allowed  ℓ  cSize vSize} → SmallerCastMeet ⁇Allowed ℓ cSize vSize → SizedCastMeet ⁇Allowed ℓ cSize vSize)
-- --   → ∀ ⁇Allowed  ℓ  cSize  vSize → SizedCastMeet ⁇Allowed ℓ cSize vSize
-- -- FixCastMeet f  =
-- --   ▹Mod.fix λ ▹self →
-- --     λ _ _ _ _ →
-- --     WFI.induction CastCompWellFounded {P = λ {(a , ℓ' , cs , vs) → SizedCastMeet a ℓ' cs vs}}
-- --       (λ {(a , ℓ' , cs , vs) → λ self → f (smallerCastMeet (self (_ , _ , _ , _)) λ {a} {ℓ'} {cs} {vs} → λ tic → ▹self tic a ℓ' cs vs)}) _
