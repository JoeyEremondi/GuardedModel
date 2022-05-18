
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
open import CodePair
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
      → ( pfc1 : (codeSize2 c1 c2)  ≡p cSize )
      → ( pfv1 : OZ  ≡p vSize )
      → (ℂ ℓ)

    oCast : ∀ {{æ : Æ}}
      → (csource cdest : ℂ ℓ)
      → ( pfc1 : codeSize2 csource cdest  ≡p cSize)
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

record SmallerCastMeet (ℓ : ℕ) (cSize vSize : Ord) : Set where
  field
    self : ∀ {cs vs : Ord} → ((cs , vs) <oPair (cSize , vSize)) → SizedCastMeet ℓ cs vs
    ℓself : ∀ {cs vs} {{ _ : 0< ℓ }} → SizedCastMeet (predℕ ℓ) cs vs
  
  ⁇_By_ : ∀ {{_ : Æ}}
      → (c : ℂ ℓ) → codeSize c <o cSize → (El c)
  ⁇_By_ c lt = o⁇ (self (<oPairL lt)) c reflp reflp

  [_]⁇_By_ : ∀ (æ : Æ)
      → (c : ℂ ℓ) → codeSize c <o cSize → (El {{æ = æ}} c)
  [_]⁇_By_ æ  = ⁇_By_ {{æ}}

  _∋_⊓_By_ : ∀ {{_ : Æ}}
      → (c : ℂ ℓ)
      → (x y : El c)
      → (codeSize c <o cSize)
      → LÆ (El c)
  _∋_⊓_By_   c x y lt =
      oMeet (self ( (<oPairL lt))) c x y reflp reflp
  [_]_∋_⊓_By_ : ∀ (æ : Æ)
      → (c : ℂ ℓ)
      → (x y : El {{æ = æ}} c)
      → (codeSize c <o cSize)
      → LÆ {{æ = æ}} (El {{æ = æ}} c)
  [_]_∋_⊓_By_ æ = _∋_⊓_By_ {{æ}}

  _⊓_By_ :
      (c1 c2 : ℂ ℓ)
      → (codeSize2 c1 c2 <o cSize)
      → (ℂ ℓ)
  _⊓_By_  c1 c2 lt =
      oCodeMeet (self (<oPairL lt)) c1 c2 reflp reflp

  ⟨_⇐_⟩_By_ : ∀ {{_ : Æ}}
      → (cdest csource : ℂ ℓ)
      → (x : El csource)
      → codeSize2 csource cdest <o cSize
      → LÆ (El cdest)
  ⟨ cdest ⇐ csource ⟩ x By lt1 =
      oCast (self ((<oPairL lt1))) csource cdest reflp x reflp

  [_]⟨_⇐_⟩_By_ : ∀ (æ : Æ)
      → (cdest csource : ℂ ℓ)
      → (x : El {{æ = æ}} csource)
      → codeSize2 csource cdest <o cSize
      → LÆ {{æ = æ}} (El {{æ = æ}} cdest)
  [_]⟨_⇐_⟩_By_ æ = ⟨_⇐_⟩_By_ {{æ}}
