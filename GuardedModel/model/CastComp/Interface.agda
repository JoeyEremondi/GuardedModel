
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
    o⁇ : ∀ {{_ : Æ}}  → (c : ℂwf ℓ)
      → (pfc1 : wfSize c ≡p cSize )
      → ( pfv2 : OZ ≡p vSize )
      → (wfEl c)
    oMeet : ∀ {{_ : Æ}}
      → (c : ℂwf ℓ)
      → (x y : wfEl c)
      → ( pfc1 : (wfSize c)  ≡p cSize )
      → ( pfv1 : omax (wfElSize c x) (wfElSize c y)  ≡p vSize )
      → LÆ (wfEl c)

    oCodeMeet :
      (c1 c2 : ℂwf ℓ)
      → ( pfc1 : (wfPairSize c1 c2)  ≡p cSize )
      → ( pfv1 : OZ  ≡p vSize )
      → (ℂwf ℓ)

    oCast : ∀ {{_ : Æ}}
      → (csource cdest : ℂwf ℓ)
      → ( pfc1 : wfPairSize csource cdest  ≡p cSize)
      →  (x : wfEl csource)
      → ( pfv1 : wfElSize csource x ≡p vSize)
      -> LÆ ( wfEl cdest)

    -- Take a code and approximate it until it is as small as the other code
    -- Used to convert to and from the germ of an inductive type
    -- Eventually we'll prove as a meta-theorem that this is the identity for well-formed inductive types
    -- TODO: is this the wrong approach?
    truncateCode : ∀ {ℓ} → (c1 c2 : ℂ ℓ)
      → (codeSize c1 ≡p cSize)
      → (OZ c1 ≡p vSize)
      → Σ[ c ∈ ℂ ℓ ](codeSize c ≤o codeSize c1)

open SizedCastMeet

record SmallerCastMeet (ℓ : ℕ) (cSize vSize : Ord) : Set where
  field
    self : ∀ {cs vs : Ord} → ((cs , vs) <oPair (cSize , vSize)) → SizedCastMeet ℓ cs vs
    ℓself : ∀ {cs vs} {{ _ : 0< ℓ }} → SizedCastMeet (predℕ ℓ) cs vs
  
  ⁇_By_ : ∀ {{_ : Æ}}
      → (c : ℂwf ℓ) → wfSize c <o cSize → (wfEl c)
  ⁇_By_ c lt = o⁇ (self (<oPairL lt)) c reflp reflp

  [_]⁇_By_ : ∀ (æ : Æ)
      → (c : ℂwf ℓ) → wfSize c <o cSize → (wfEl {{æ = æ}} c)
  [_]⁇_By_ æ  = ⁇_By_ {{æ}}

  _∋_⊓_By_ : ∀ {{_ : Æ}}
      → (c : ℂwf ℓ)
      → (x y : wfEl c)
      → (wfSize c <o cSize)
      → LÆ (wfEl c)
  _∋_⊓_By_   c x y lt =
      oMeet (self ( (<oPairL lt))) c x y reflp reflp
  [_]_∋_⊓_By_ : ∀ (æ : Æ)
      → (c : ℂwf ℓ)
      → (x y : wfEl {{æ = æ}} c)
      → (wfSize c <o cSize)
      → LÆ {{æ = æ}} (wfEl {{æ = æ}} c)
  [_]_∋_⊓_By_ æ = _∋_⊓_By_ {{æ}}

  _⊓_By_ :
      (c1 c2 : ℂwf ℓ)
      → (wfPairSize c1 c2 <o cSize)
      → (ℂwf ℓ)
  _⊓_By_  c1 c2 lt =
      oCodeMeet (self (<oPairL lt)) c1 c2 reflp reflp

  ⟨_⇐_⟩_By_ : ∀ {{_ : Æ}}
      → (cdest csource : ℂwf ℓ)
      → (x : wfEl csource)
      → wfPairSize csource cdest <o cSize
      → LÆ (wfEl cdest)
  ⟨ cdest ⇐ csource ⟩ x By lt1 =
      oCast (self ((<oPairL lt1))) csource cdest reflp x reflp

  [_]⟨_⇐_⟩_By_ : ∀ (æ : Æ)
      → (cdest csource : ℂwf ℓ)
      → (x : wfEl {{æ = æ}} csource)
      → wfPairSize csource cdest <o cSize
      → LÆ {{æ = æ}} (wfEl {{æ = æ}} cdest)
  [_]⟨_⇐_⟩_By_ æ = ⟨_⇐_⟩_By_ {{æ}}
open SmallerCastMeet {{...}} public
