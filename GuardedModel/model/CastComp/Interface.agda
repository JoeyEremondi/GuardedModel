
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

module CastComp.Interface {{_ : DataTypes}} {{_ : DataGerms}} {{_ : InductiveCodes}} {{_ : DataGermsSmaller}}  where

open import Code
open import Head
open import Util
open import Ord
-- open Ord ℂ El ℧ C𝟙 refl


open import Germ
record SizedCastMeet (ℓ : ℕ) (cSize vSize : Ord) : Set where
  field
    o⁇ : ∀ {{æ : Æ}}  → (c : ℂ ℓ)
      → (pfc1 : codeSize c ≡p cSize )
      → ( pfv2 : OZ ≡p vSize )
      → (El c)
    oMeet : ∀ {{æ : Æ}}
      → (c : ℂ ℓ)
      → (x y : El c)
      → ( pfc1 : (codeSize c)  ≡p cSize )
      → ( pfv1 : omax (elSize c x) (elSize c y)  ≡p vSize )
      → LÆ (El c)



    oCodeMeet :
      (c1 c2 : ℂ ℓ)
      → ( pfc1 : omax (codeSize c1) (codeSize c2)  ≡p cSize )
      → ( pfv1 : OZ  ≡p vSize )
      → (ℂ ℓ)

    oCodeMeetSize :
      (c1 c2 : ℂ ℓ)
      → ( pfc1 : omax (codeSize c1) (codeSize c2)  ≡p cSize )
      → ( pfv1 : OZ  ≡p vSize )
      → codeSize (oCodeMeet c1 c2 pfc1 pfv1) ≤o omax (codeSize c1) (codeSize c2)

    oCast : ∀ {{æ : Æ}}
      → (csource cdest : ℂ ℓ)
      → ( pfc1 : omax (codeSize csource) (codeSize cdest)  ≡p cSize)
      →  (x : El csource)
      → ( pfv1 : elSize csource x ≡p vSize)
      -> LÆ ( El cdest)

    -- Take a code and approximate it until it is as small as the other code
    -- Used to convert to and from the germ of an inductive type
    -- Eventually we'll prove as a meta-theorem that this is the identity for well-formed inductive types
    -- TODO: is this the wrong approach?
    truncateCode : ∀ {ℓ} → (c1 c2 : ℂ ℓ)
      → (codeSize c1 ≡p cSize)
      → (OZ ≡p vSize)
      → Σ[ c ∈ ℂ ℓ ](codeSize c ≤o codeSize c1)

open SizedCastMeet public

data Hide (a : Set) : Set where
  hide : ∀ {arg : a} → Hide a

reveal : ∀ {a} → Hide a → a
reveal (hide {arg = x}) = x

record SmallerCastMeet (ℓ : ℕ) (cSize vSize : Ord) : Set where
  field
    self : ∀ {cs vs : Ord} → ((cs , vs) <oPair (cSize , vSize)) → SizedCastMeet ℓ cs vs
    ℓself : ∀ {cs vs} {{ inst : 0< ℓ }} → SizedCastMeet (predℕ ℓ) cs vs
  infix 20 ⁇_By_
  ⁇_By_ : ∀ {{_ : Æ}}
      → (c : ℂ ℓ) → (lt : Hide (codeSize c <o cSize)) → (El c)
  ⁇_By_ c (hide {lt}) = o⁇ (self (<oPairL lt)) c reflp reflp

  infix 20 [_]⁇_By_
  [_]⁇_By_ : ∀ (æ : Æ)
      → (c : ℂ ℓ) → (lt : Hide (codeSize c <o cSize)) → (El {{æ = æ}} c)
  [_]⁇_By_ æ  = ⁇_By_ {{æ}}

  infix 20 _∋_⊓_By_
  _∋_⊓_By_ : ∀ {{_ : Æ}}
      → (c : ℂ ℓ)
      → (x y : El c)
      → (lt : Hide (codeSize c <o cSize))
      → LÆ (El c)
  _∋_⊓_By_   c x y (hide {lt}) =
      oMeet (self ( (<oPairL lt))) c x y reflp reflp

  infix 20 [_]_∋_⊓_By_
  [_]_∋_⊓_By_ : ∀ (æ : Æ)
      → (c : ℂ ℓ)
      → (x y : El {{æ = æ}} c)
      → (lt : Hide (codeSize c <o cSize))
      → LÆ {{æ = æ}} (El {{æ = æ}} c)
  [_]_∋_⊓_By_ æ = _∋_⊓_By_ {{æ}}


  infix 20 _⊓_By_
  _⊓_By_ :
      (c1 c2 : ℂ ℓ)
      → (lt : Hide (omax (codeSize c1) (codeSize c2) <o cSize))
      → (ℂ ℓ)
  _⊓_By_  c1 c2 (hide {lt}) =
      oCodeMeet (self (<oPairL lt)) c1 c2 reflp reflp


  infix 20 _⊓Size_By_
  _⊓Size_By_ :
      (c1 c2 : ℂ ℓ)
      → (lt : Hide (omax (codeSize c1) (codeSize c2) <o cSize))
      →  codeSize (c1 ⊓ c2 By lt ) ≤o omax (codeSize c1) (codeSize c2)
  _⊓Size_By_  c1 c2 (hide {lt}) =
      oCodeMeetSize (self (<oPairL lt)) c1 c2 reflp reflp

  infix 20 ⟨_⇐_⟩_By_
  ⟨_⇐_⟩_By_ : ∀ {{_ : Æ}}
      → (cdest csource : ℂ ℓ)
      → (x : El csource)
      → (lt : Hide (omax (codeSize csource)  (codeSize cdest) <o cSize))
      → LÆ (El cdest)
  ⟨_⇐_⟩_By_ cdest csource x (hide {lt}) =
      oCast (self ((<oPairL lt))) csource cdest reflp x reflp

  infix 20 [_]⟨_⇐_⟩_By_
  [_]⟨_⇐_⟩_By_ : ∀ (æ : Æ)
      → (cdest csource : ℂ ℓ)
      → (x : El {{æ = æ}} csource)
      → (lt : Hide (omax (codeSize csource)  (codeSize cdest) <o cSize))
      → LÆ {{æ = æ}} (El {{æ = æ}} cdest)
  [_]⟨_⇐_⟩_By_ æ = ⟨_⇐_⟩_By_ {{æ}}

  -- Helper to manage the common case of having two elements of different codes' types,
  -- casting them to the meet code, then taking the meet of those two elements
  infix 20 _,_∋_⊓_By_
  _,_∋_⊓_By_ :
    ∀ {{æ : Æ}} c1 c2 →
      (El c1) →
      (El c2) →
      (lt∞ : Hide (omax (omax∞ (codeSize c1)) (omax∞ (codeSize c2)) <o cSize)) →
      LÆ (El (c1 ⊓ c2 By hide {arg = ≤∘<-in-< (omax-mono (omax∞-self _) (omax∞-self _)) (reveal lt∞)}))
  _,_∋_⊓_By_ c1 c2 x1 x2 (hide {arg = lt∞}) = do
   let lt = ≤∘<-in-< (omax-mono (omax∞-self _) (omax∞-self _)) (lt∞)
   let c12 = (c1 ⊓ c2 By hide {arg = lt})
   let
     lt1 =
       ≤o-sucMono
         (omax-monoR (c1 ⊓Size c2 By hide {arg = lt})
         ≤⨟ omax-assocL (codeSize c1) (codeSize c1) (codeSize c2)
         ≤⨟ omax-mono (omax∞-idem∞ _) (omax∞-self _)
         )
         ≤⨟ lt∞
   let
     lt2 =
       ≤o-sucMono (
         omax-monoR (c1 ⊓Size c2 By hide {arg = lt} ≤⨟ omax-commut _ _)
         ≤⨟ omax-assocL _ _ _ 
         ≤⨟ omax-commut _ _
         ≤⨟ omax-mono (omax∞-self _) (omax∞-idem∞ _)
         )
       ≤⨟ lt∞
   let
     lt12 =
       ≤o-sucMono (
         (c1 ⊓Size c2 By hide {arg = lt})
         ≤⨟ omax-mono (omax∞-self _) (omax∞-self _))
       ≤⨟ lt∞
   x1-12 ←  (⟨ c12 ⇐ c1 ⟩ x1 By
        hide {arg = lt1 })
   x2-12 ←  (⟨ c12 ⇐ c2 ⟩ x2 By hide {arg = lt2})
   c12 ∋ x1-12 ⊓ x2-12 By hide {arg = lt12 }
