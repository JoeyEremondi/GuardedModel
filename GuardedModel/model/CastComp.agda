

{-# OPTIONS --cubical --guarded #-}

-- open import Guarded
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

module CastComp {{_ : DataTypes}} {{_ : DataGerms}} {{_ : InductiveCodes}} {{_ : DataGermsSmaller}} where

open import Code
open import Head
open import Util
open import Ord
-- open Ord ℂ El ℧ C𝟙 refl


open import Germ



record CastMeet (cSize vSize : Ord) : Set where
  field
    o⁇ : ∀ {{_ : Æ}} {ℓ} → (c : ℂ ℓ)
      → {@(tactic default (reflp {A = Ord} {cSize})) pf : codeSize c ≡p cSize }
      → {@(tactic default (reflp {A = Ord} {O1})) pf : O1 ≡p vSize }
      → LÆ (El c)
    oMeet : ∀ {{_ : Æ}} {ℓ}
      → (c : ℂ ℓ)
      → (x y : El c)
      → {@(tactic default (reflp {A = Ord} {cSize})) pf : (codeSize c)  ≡p cSize }
      → {@(tactic default (reflp {A = Ord} {vSize})) pf2 : omax (elSize c x) (elSize c y)  ≡p vSize }
      → LÆ (El c)
    oToGerm : ∀ {{_ : Æ}}{ℓ h} → (c : ℂ ℓ)
      → {@(tactic default (reflp {A = Ord} {cSize})) pf : (codeSize c) ≡p cSize }
      → codeHead c ≡p HStatic h
      → (x : El c)
      → {@(tactic default (reflp {A = Ord} {vSize})) pf2 : elSize c x ≡p vSize }
      → LÆ (germ h ℓ)
    oFromGerm : ∀ {{_ : Æ}}{ℓ h} → (c : ℂ ℓ)
      → {@(tactic default (reflp {A = Ord} {cSize})) pf : (codeSize c) ≡p cSize }
      → codeHead c ≡p HStatic h
      → (x : germ h ℓ)
      → {@(tactic default (reflp {A = Ord} {vSize})) pf2 : O1 ≡p vSize }
      → LÆ (El c)

    oToDataGerm : ∀ {{_ : Æ}}{ℓ} {cI cB : ℂ ℓ} (tyCtor : CName) (D : DName tyCtor → ℂDesc cI C𝟙 )
      → {i : ApproxEl cI}
      → {@(tactic default (reflp {A = Ord} {cSize})) pf : omax (codeSize (Cμ tyCtor cI D i)) (dataGermDescSize ℓ tyCtor)  ≡p cSize }
      → (x : ℂμ tyCtor D i)
      → {@(tactic default (reflp {A = Ord} {vSize})) pf2 : elSize (Cμ tyCtor cI D i) (transport ℂμW x)  ≡p vSize }
      → W (germContainer ℓ tyCtor (▹⁇ ℓ)) (⁇Ty ℓ) tt


    oCast : ∀ {{_ : Æ}}{ℓ}
      → (c₁ c₂ : ℂ ℓ)
      → {@(tactic default (reflp {A = Ord} {cSize})) pf : omax (codeSize c₁) (codeSize c₂) ≡p cSize}
      →  (x : El c₁)
      → {@(tactic default (reflp {A = Ord} {vSize})) pf2 : elSize c₁ x ≡p vSize}
      -> LÆ ( El c₂)

open CastMeet


castMeetRec :  (cSize vSize : Ord)  →
      (self : ∀ {cs' vs' : Ord} → ((cs' , vs') <oo (cSize , vSize)) → CastMeet cs' vs') →  CastMeet cSize vSize
castMeetRec cSize vSize self = record
                          { o⁇ = ⁇ ; oMeet = meet ; oToGerm = toGerm ; oFromGerm = fromGerm ; oCast = cast }
  where
    ⁇ : ∀ {{_ : Æ}} {ℓ} → (c : ℂ ℓ)
      → {@(tactic default (reflp {A = Ord} {cSize})) pf : codeSize c ≡p cSize }
      → {@(tactic default (reflp {A = Ord} {O1})) pf2 : O1 ≡p vSize }
      → LÆ (El c)
    ⁇ CodeModule.C⁇ {reflp} = pure ⁇⁇
    ⁇ CodeModule.C℧ {reflp} = pure tt
    ⁇ CodeModule.C𝟘 {reflp} = pure tt
    ⁇ CodeModule.C𝟙 {reflp} = pure true
    ⁇ {suc ℓ} CodeModule.CType {reflp} = pure C⁇
    ⁇ (CodeModule.CΠ dom cod) {reflp} = liftFunDep
      λ x →
       self (≤oo-sucL (≤o-trans (≤o-cocone {{æ = Approx}} _ (approx x) (≤o-refl _)) omax-≤R))
         .o⁇ (cod (approx x))
    ⁇ {{æ}} (CodeModule.CΣ dom cod) {reflp} = do
        ⁇x ← withApproxL λ æ →
           self (≤oo-sucL (≤o-trans (≤o-refl _) omax-≤L))
           .o⁇ {{æ}} dom
        --TODO: problem is monadic bind isn't polymorphic enough in Æ
        ⁇y ← self  (≤oo-sucL (≤o-trans (≤o-cocone {{æ = Approx}} _ (approx ⁇x) (≤o-refl _)) omax-≤R))
          .o⁇ (cod (approx ⁇x))
        pure (⁇x , ⁇y)
    ⁇ (CodeModule.C≡ c x y) {reflp} = do
      wit ← self  (<ooL (≤o-sucMono omax-≤L))
        .oMeet {{Approx}} c x y
      pure (wit ⊢ x ≅ y)
    ⁇ (CodeModule.Cμ tyCtor c D x) {reflp} = pure W⁇

    -- codeMeet   : ∀ {ℓ}
    --   → (x y : ℂ ℓ)
    --   → {@(tactic default (reflp {A = Ord} {size})) pf : omax (codeSize x) (codeSize y) ≡p size }
    --   → LÆ (ℂ ℓ)

    meet   : ∀ {{_ : Æ}} {ℓ}
      → (c : ℂ ℓ)
      → (x y : El c)
      → {@(tactic default (reflp {A = Ord} {cSize})) pf : (codeSize c) ≡p cSize }
      → {@(tactic default (reflp {A = Ord} {vSize})) pf2 : omax (elSize c x) (elSize c y)  ≡p vSize }
      → LÆ (El c)
    meet c x y with codeHead c in eqc
    ... | ch with valueHead c eqc x in eq1 | valueHead c eqc y in eq2 | valHeadMatchView (valueHead c eqc x) (valueHead c eqc y)
    -- If either arg is bottom or there is a head mismatch, produce error
    ... |  h1 |  h2 |  VH℧L x₁ = pure (℧ c)
    ... |  h1 |  h2 |  VH℧R x₁ = pure (℧ c)
    ... |  .(HVIn⁇ _ _) |  .(HVIn⁇ _ _) |  VHNeq⁇ x₁ = pure (℧ c)
    ... |  .(HVal _) |  .(HVal _) |  VHNeq x₁ = pure (℧ c)
    -- If either is ⁇, then return the other argument
    ... |  h1 |  h2 |  VH⁇L x₁ x₂ = pure y
    ... |  .(HVal _) |  h2 |  VH⁇R x₁ = pure x
    ... |  h1 |  h2 |  VHIn⁇L x₁ x₂ = pure y
    ... |  .(HVIn⁇ _ _) |  h2 |  VHIn⁇R x₁ = pure x
    -- Otherwise the head matches, so we do case-analysis on the type to see how to proceed
    meet CodeModule.C𝟙 true true {reflp} | .(HStatic _)  | .(HVal _)  | .(HVal _)  | VHEq reflp
      = pure true
    meet {ℕ.suc ℓ} CodeModule.CType x y | HStatic HType  | HVal h  | .(HVal _)  | VHEq reflp = {!!}
    -- The meet of two functions is the function that takes the meet of the two arguments
    meet (CodeModule.CΠ dom cod) f1 f2 {reflp} | .(HStatic _)  | .(HVal _)  | .(HVal _)  | VHEq reflp
      = liftFunDep λ x →
        self (≤oo-sucL (≤o-trans (≤o-cocone {{æ = Approx}} _ (approx  x) (≤o-refl _)) omax-≤R))
          .oMeet (cod (approx x)) (f1 x) (f2 x)
    -- To take the meet of dependent pairs, we take the meet of the first elements
    -- then cast the seconds to the codomain applied to the meet of the firsts
    -- and take their meet
    meet {{æInit}} (CodeModule.CΣ dom cod) (x1 , x2) (y1 , y2) {reflp} {pf2} | .(HStatic _)  | .(HVal _)  | .(HVal _)  | VHEq reflp =  do
      xy1 ← withApproxL' λ æ conv → self (≤oo-sucL omax-≤L)
        .oMeet {{æ}} dom (exact {{æ}} (conv x1) ) (exact {{æ}} (conv y1))
      x2cast ← self (≤oo-sucL (≤o-trans (omax-LUB (≤o-cocone {{æ = Approx}} _ (approx x1) (≤o-refl _)) (≤o-cocone {{æ = Approx}} _ (approx xy1) (≤o-refl _))) omax-≤R))
        .oCast (cod (approx x1)) (cod (approx xy1)) x2
      y2cast ← self (≤oo-sucL (≤o-trans (omax-LUB (≤o-cocone {{æ = Approx}} _ (approx y1) (≤o-refl _)) (≤o-cocone {{æ = Approx}} _ (approx xy1) (≤o-refl _))) omax-≤R))
        .oCast (cod (approx y1)) (cod (approx xy1)) y2
      xy2 ← self (≤oo-sucL (≤o-trans (≤o-cocone {{æ = Approx}} _ (approx xy1) (≤o-refl _)) omax-≤R))
        .oMeet (cod (approx xy1)) x2cast y2cast
      pure (xy1 , xy2)
    --Meet of two equality proofs is just the meet of their witnesses
    meet (CodeModule.C≡ c x₁ y₁) (w1 ⊢ _ ≅ _) (w2 ⊢ _ ≅ _) {reflp} | .(HStatic _)  | .(HVal _)  | .(HVal _)  | VHEq reflp = do
      w12 ← self (≤oo-sucL omax-≤L)
        .oMeet {{Approx}} c w1 w2
      pure (w12 ⊢ x₁ ≅ y₁)
    meet (CodeModule.Cμ tyCtor c D x₁) x y | .(HStatic _)  | .(HVal _)  | .(HVal _)  | VHEq reflp = {!!}
    ... |  .(HVIn⁇ _ _) |  .(HVIn⁇ _ _) |  VHEq⁇ x₁ = {!!}

    toGerm : ∀ {{ _ : Æ}} {ℓ h} → (c : ℂ ℓ)
      → {@(tactic default (reflp {A = Ord} {cSize})) pf : (codeSize c) ≡p cSize }
      → codeHead c ≡p HStatic h
      → (x : El c)
      → {@(tactic default (reflp {A = Ord} {vSize})) pf2 : elSize c x ≡p vSize }
      → LÆ (germ h ℓ)
--     toGerm CodeModule.C⁇ {reflp} () x
--     toGerm CodeModule.C℧ {reflp} () x
--     toGerm CodeModule.C𝟘 {reflp} reflp x = pure tt
--     toGerm CodeModule.C𝟙 {reflp} reflp x = pure x
--     toGerm {suc ℓ} CodeModule.CType {reflp} reflp x = pure x
--     toGerm (CodeModule.CΠ dom cod) {reflp} reflp f = liftFun λ x → do
--       x⁇ ←
--         self (≤oo-sucL (≤o-trans (codeMaxL dom) omax-≤L))
--           .oCast C⁇ dom x
--       self (≤oo-sucL (≤o-trans (codeMaxR (cod (approx x⁇))) (≤o-trans (≤o-cocone _ x⁇ (≤o-refl _)) omax-≤R)))
--         .oCast (cod (approx x⁇)) C⁇ (f x⁇)
--     toGerm (CodeModule.CΣ c cod) {reflp} reflp x = {!!}
--     toGerm (CodeModule.C≡ c x₁ y) {reflp} reflp x = {!!}
--     toGerm (CodeModule.Cμ tyCtor c D x₁) {reflp} reflp x = {!!}

    fromGerm : ∀ {{_ : Æ}} {ℓ h} → (c : ℂ ℓ)
      → {@(tactic default (reflp {A = Ord} {cSize})) pf : (codeSize c) ≡p cSize }
      → codeHead c ≡p HStatic h
      → (x : germ h ℓ)
      → {@(tactic default (reflp {A = Ord} {vSize})) pf2 : O1 ≡p vSize }
      → LÆ (El c)

    cast : ∀ {{_ : Æ}} {ℓ}
      → (c₁ c₂ : ℂ ℓ)
      → {@(tactic default (reflp {A = Ord} {cSize})) pf : omax (codeSize c₁) (codeSize c₂) ≡p cSize}
      →  (x : El c₁)
      → {@(tactic default (reflp {A = Ord} {vSize})) pf2 : elSize c₁ x ≡p vSize}
      -> LÆ ( El c₂)




-- -- -- castMeetRec : (size : Ord) →
-- -- --       (self : {y : Ord} → (y <o size) → CastMeet y) → CastMeet size
-- -- -- CastMeet.oCast (castMeetRec size self) c₁ c₂ x with codeHead c₁ in eq1 | codeHead c₂ in eq2 | headMatchView (codeHead c₁) (codeHead c₂)
-- -- -- -- Casting from ℧ is always error
-- -- -- ... | h1 |  h2 |  H℧L x₁ = pure (℧ c₂ )
-- -- -- -- Casting to ℧ is always error
-- -- -- ... | h1 |  h2 |  H℧R x₁ = pure (℧ c₂)
-- -- -- -- Casting between types with different heads is an error
-- -- -- ... | .(HStatic _) |  .(HStatic _) |  HNeq x₁ = pure (℧ c₂)
-- -- -- ... | h1 |  H℧ |  H⁇L x₁ x₂ with () ← x₂ reflp
-- -- -- --Casting from a type to ⁇
-- -- -- oCast (castMeetRec .(codeSize {ℓ} c₁ +o codeSize {ℓ} C⁇) self) {ℓ} c₁ CodeModule.C⁇ {reflp} x | (HStatic h) |  .H⁇ |  H⁇R reflp = do
-- -- --   xgerm ← self {!!} .oToGerm c₁ (ptoc eq1) x
-- -- --   pure (germTo⁇ {h = h} xgerm)
-- -- -- -- Casting from ⁇ to a type
-- -- -- -- If the target type is ⁇, we don't have to do anything
-- -- -- CastMeet.oCast (castMeetRec size self) CodeModule.C⁇ CodeModule.C⁇ x | .H⁇ |  H⁇ |  H⁇L reflp x₂ = pure x
-- -- -- -- If the destination type has a static head, we check what value we have from ⁇
-- -- -- CastMeet.oCast (castMeetRec size self) CodeModule.C⁇ c₂ x | .H⁇ |  HStatic h2 |  H⁇L reflp x₂ with valueHead C⁇ reflp x in eq
-- -- -- -- If it is ⁇, produce ⁇ at the target type
-- -- -- CastMeet.oCast (castMeetRec size self) CodeModule.C⁇ c₂ {reflp} x | .H⁇ |  HStatic h2 |  H⁇L reflp x₂ | VH⁇⁇ = pure (self (≤o-refl _) .o⁇  c₂)
-- -- -- -- If it is ℧, produce ℧ at the target type
-- -- -- CastMeet.oCast (castMeetRec size self) CodeModule.C⁇ c₂ x | .H⁇ |  HStatic h2 |  H⁇L reflp x₂ | VH℧ = pure (℧ c₂)
-- -- -- -- Otherwise, we check if the value's head matches the target type
-- -- -- CastMeet.oCast (castMeetRec size self) CodeModule.C⁇ c₂ {reflp} x | .H⁇ |  HStatic h2 |  H⁇L reflp x₂ | HVIn⁇ h1 hrest with headDecEq h1 h2
-- -- --   -- If the value from ⁇ has the same head as the target code, then we cast through the germ
-- -- -- ... | yes reflp = do
-- -- --   xgerm ← germFrom⁇ x eq
-- -- --   self {!!} .oFromGerm c₂ (ptoc eq2) xgerm
-- -- -- -- Otherwise, we produce an error
-- -- -- ... | no neq = pure (℧ c₂)
-- -- -- CastMeet.oCast (castMeetRec size self) (CΠ c₁ cod) (CΠ c₂ cod₁) x | HStatic HΠ |  .(HStatic HΠ) |  HEq reflp = {!!}
-- -- -- CastMeet.oCast (castMeetRec size self) (CΣ c₁ cod) (CΣ c₂ cod₁) x | HStatic HΣ |  .(HStatic HΣ) |  HEq reflp = {!!}
-- -- -- CastMeet.oCast (castMeetRec size self) (C≡ c₁ x₁ y) (C≡ c₂ x₂ y₁) x | HStatic H≅ |  .(HStatic H≅) |  HEq reflp = do

-- -- --   pure {!!}
-- -- -- CastMeet.oCast (castMeetRec size self) C𝟙 C𝟙 x | HStatic H𝟙 |  .(HStatic H𝟙) |  HEq reflp = pure x
-- -- -- CastMeet.oCast (castMeetRec size self) C𝟘 C𝟘 x | HStatic H𝟘 |  .(HStatic H𝟘) |  HEq reflp = pure x
-- -- -- CastMeet.oCast (castMeetRec size self) {suc ℓ} CType CType x | HStatic HType |  .(HStatic HType) |  HEq reflp = pure x
-- -- -- CastMeet.oCast (castMeetRec size self) (Cμ tyCtor c₁ D x₁) (Cμ tyCtor₁ c₂ D₁ x₂) x | HStatic (HCtor x₃) |  .(HStatic (HCtor x₃)) |  HEq reflp = {!!}

-- -- -- CastMeet.oMeet (castMeetRec size self) c x y {reflp} with codeHead c in eqc
-- -- -- ... | ch with valueHead c eqc x in eq1 | valueHead c eqc y in eq2 | valHeadMatchView (valueHead c eqc x) (valueHead c eqc y)
-- -- -- -- If either arg is ℧ or the heads don't match, produce an error
-- -- -- ... |  h1 |  h2 |  VH℧L x₁ = pure (℧ c)
-- -- -- ... |  h1 |  h2 |  VH℧R x₁ = pure (℧ c)
-- -- -- ... |  .(HVal _) |  .(HVal _) |  VHNeq x₁ = pure (℧ c)
-- -- -- ... |  .(HVIn⁇ _ _) |  .(HVIn⁇ _ _) |  VHNeq⁇ x₁ = pure (℧ c)
-- -- -- -- If either arg is ⁇, return the other argu
-- -- -- ... |  h1 |  h2 |  VH⁇L x₁ x₂ = pure y
-- -- -- ... |  .(HVal _) |  h2 |  VH⁇R x₁ = pure x
-- -- -- ... |  h1 |  h2 |  VHIn⁇L x₁ x₂ = pure y
-- -- -- ... |  .(HVIn⁇ _ _) |  h2 |  VHIn⁇R x₁ = pure x
-- -- -- -- Meet when the head matches
-- -- -- -- Unit: nothing to do, just produce unit
-- -- -- oMeet (castMeetRec .(codeSize {ℓ} CodeModule.C𝟙) self) {ℓ} CodeModule.C𝟙 x y {reflp} | .(HStatic _) |  HVal h |  HVal h |  VHEq reflp
-- -- --   = pure true
-- -- -- -- Types: head must match, so just take the meet of the parts
-- -- -- oMeet (castMeetRec .(codeSize (CodeModule.CType )) self) {suc ℓ} CodeModule.CType  x y {reflp} | .(HStatic _) |  HVal h |  HVal h |  VHEq reflp
-- -- --   = {!!}
-- -- -- -- Functions: make the function that takes the meet of the result of the given functions
-- -- -- oMeet (castMeetRec .(codeSize (CodeModule.CΠ dom cod)) self) (CodeModule.CΠ dom cod) f1 f2 {reflp} | .(HStatic _) |  HVal h |  HVal h |  VHEq reflp
-- -- --   = liftFunDep (λ x →
-- -- --     self (≤o-sucMono (≤o-trans (≤o-cocone (λ x₁ → codeSize (cod x₁)) x (≤o-refl (codeSize (cod x)))) omax-≤R))
-- -- --       .oMeet (cod x) (f1 x) (f2 x))
-- -- -- oMeet (castMeetRec .(codeSize (CodeModule.CΣ dom cod)) self) (CodeModule.CΣ dom cod) (x1 , x2) (y1 , y2) {reflp} | .(HStatic _) |  HVal h |  HVal h |  VHEq reflp
-- -- --   = do
-- -- --     xy1 ←
-- -- --       self (≤o-sucMono (omax-≤L))
-- -- --         .oMeet dom x1 y1
-- -- --     x2cast ←
-- -- --       self (≤o-sucMono (≤o-trans {!!} omax-≤R))
-- -- --         .oCast (cod x1) (cod xy1) x2
-- -- --     xy2 ←
-- -- --       self {!!}
-- -- --         .oMeet (cod xy1) {!!} {!!}
-- -- --     pure {!!}
-- -- -- oMeet (castMeetRec .(codeSize (CodeModule.C≡ c x₁ y₁)) self) (CodeModule.C≡ c x₁ y₁) x y {reflp} | .(HStatic _) |  HVal h |  HVal h |  VHEq reflp
-- -- --   = {!!}
-- -- -- oMeet (castMeetRec .(codeSize (CodeModule.Cμ tyCtor c D x₁)) self) (CodeModule.Cμ tyCtor c D x₁) x y {reflp} | .(HStatic _) |  HVal h |  HVal h |  VHEq reflp
-- -- --   = {!!}
-- -- -- -- Meet for elements of ⁇ when the head matches
-- -- -- ... |  .(HVIn⁇ _ _) |  .(HVIn⁇ _ _) |  VHEq⁇ x₁ = {!!}
-- -- -- -- oMeet (castMeetRec .(codeSize CodeModule.C℧) self) CodeModule.C℧ x y {reflp} | h1 |  h2 |  v | H℧  = pure tt
-- -- -- CastMeet.oToGerm (castMeetRec size self) = {!!}
-- -- -- CastMeet.oFromGerm (castMeetRec size self) = {!!}
-- -- -- CastMeet.o⁇ (castMeetRec size self) = {!!}

-- -- -- -- -- ⁇ : ∀ {ℓ} → (c--  : ℂ ℓ) → El c
-- -- -- -- -- cast : ∀ {ℓ} → (c₁ c₂ : ℂ ℓ) → El c₁ -> (El c₂)
-- -- -- -- -- -- castDesc : ∀ {ℓ} (tyCtor1 tyCtor2 : CName)
-- -- -- -- -- --         → (c1 c2 : ℂ ℓ)
-- -- -- -- -- --         → (D1 : DName tyCtor1 → ℂDesc c1)
-- -- -- -- -- --         → (D2 : DName tyCtor2 → ℂDesc c2)
-- -- -- -- -- --         → (i₁ : El c1) → (i₂ : El c2)
-- -- -- -- -- --         → μ (Arg (DName tyCtor1) λ d → interpDesc (D1 d)) i₁
-- -- -- -- -- --         → (μ (Arg (DName tyCtor2) λ d → interpDesc (D2 d)) i₂)
-- -- -- -- -- toGerm : ∀ {ℓ} (c : ℂ ℓ) (h : Head) → codeHead c ≡p HStatic h → El c → germ h ℓ
-- -- -- -- -- fromGerm : ∀ {ℓ} (c : ℂ ℓ) (h : Head) → codeHead c ≡p HStatic h → germ h ℓ → El c
-- -- -- -- -- packGerm :   ∀ {ℓ} (h : Head) → germ h ℓ → ⁇Ty ℓ
-- -- -- -- -- unpackGerm :  ∀ {ℓ} (h : Head) → ⁇Ty ℓ → germ h ℓ
-- -- -- -- -- _⊓[_]_  : ∀ {ℓ} {c : ℂ ℓ} → El c → (c' : ℂ ℓ) → El c → {@(tactic default (reflp {A = ℂ ℓ} {c})) pf : c ≡p c'} → El c
-- -- -- -- -- codeMeet : ∀ {ℓ} (c1 c2 : ℂ ℓ) → ℂ ℓ


-- -- -- -- -- cast c₁ c₂ x with  codeHead c₁ in eq1 | codeHead c₂ in eq2 | headMatchView (codeHead c₁) (codeHead c₂)
-- -- -- -- -- ... | h1 | h2 | H℧L x₁ =  (℧ c₂)
-- -- -- -- -- ... | h1 | h2 | H℧R x₁ = (℧ c₂)
-- -- -- -- -- cast CodeModule.C⁇ CodeModule.C⁇ x | H⁇ |  H⁇  | H⁇L x₁ x₂ = x
-- -- -- -- -- cast c₁ CodeModule.C℧ x | H⁇ |  H℧ |  H⁇L x₁ x₂ = tt
-- -- -- -- -- ... | .(HStatic _) | .(HStatic _) | HNeq x₁ = (℧ c₂)
-- -- -- -- -- cast (CodeModule.CΠ dom1 cod1) (CodeModule.CΠ dom2 cod2) f | .(HStatic HΠ) |  .(HStatic HΠ) |  HEq {h1 = HΠ} reflp
-- -- -- -- --   = {!!}
-- -- -- -- --   -- ret
-- -- -- -- --   --  where
-- -- -- -- --   --    ret : El (CΠ dom2 cod2)
-- -- -- -- --   --    ret x2 = do
-- -- -- -- --   --      let x1 = cast dom2 dom1 x2
-- -- -- -- --   --      fx1 ← f x1
-- -- -- -- --   --      pure (cast (cod1 x1) (cod2 x2) fx1)
-- -- -- -- -- cast (CodeModule.CΣ dom1 cod1) (CodeModule.CΣ dom2 cod2) (x1 , y1) | .(HStatic HΣ) |  .(HStatic HΣ) |  HEq {h1 = HΣ} reflp
-- -- -- -- --   = let x2 = cast dom1 dom2 x1
-- -- -- -- --     in (x2 , cast (cod1 x1) (cod2 x2) y1)
-- -- -- -- -- cast (CodeModule.C≡ c₁ x₁ y) (CodeModule.C≡ c₂ x₂ y₁) (wit ⊢ _ ≅ _) | .(HStatic H≅) |  .(HStatic H≅) |  HEq {h1 = H≅} reflp
-- -- -- -- --   = cast c₁ c₂ wit ⊢ x₂ ≅ y₁
-- -- -- -- -- cast CodeModule.C𝟙 CodeModule.C𝟙 x | .(HStatic H⊤) |  .(HStatic H⊤) |  HEq {h1 = H⊤} reflp
-- -- -- -- --   = x
-- -- -- -- -- cast CodeModule.C𝟘 CodeModule.C𝟘 x | .(HStatic H⊥) |  .(HStatic H⊥) |  HEq {h1 = H⊥} reflp
-- -- -- -- --   = x
-- -- -- -- -- cast CodeModule.CType CodeModule.CType x | .(HStatic HType) |  .(HStatic HType) |  HEq {h1 = HType} reflp
-- -- -- -- --   = x
-- -- -- -- -- cast (CodeModule.Cμ tyCtor1 c₁ D x₁) (CodeModule.Cμ tyCtor2 c₂ D₁ x₂) x | .(HStatic (HCtor x₃)) |  .(HStatic (HCtor x₃)) |  HEq {h1 = HCtor x₃} reflp
-- -- -- -- --   = {!!} --castDesc tyCtor1 tyCtor2 c₁ c₂ D D₁ x₁ x₂ x
-- -- -- -- -- cast C⁇ c₂ x | H⁇ | HStatic h | H⁇L x₁ x₂
-- -- -- -- --   = fromGerm c₂ h eq2 (unpackGerm h x)
-- -- -- -- -- cast c₁ C⁇ x | (HStatic h) |  H⁇ |  H⁇R x₁
-- -- -- -- --   = packGerm h (toGerm c₁ h eq1 x)



-- -- -- -- -- ⁇ CodeModule.C⁇ = ⁇⁇
-- -- -- -- -- ⁇ CodeModule.C℧ = tt
-- -- -- -- -- ⁇ CodeModule.C𝟘 = tt
-- -- -- -- -- ⁇ CodeModule.C𝟙 = true
-- -- -- -- -- ⁇ {suc ℓ} CodeModule.CType = C⁇
-- -- -- -- -- ⁇ (CodeModule.CΠ dom cod) = λ x → {!!} --pure (⁇ (cod x))
-- -- -- -- -- ⁇ (CodeModule.CΣ dom cod) = ⁇ dom , ⁇ (cod (⁇ dom))
-- -- -- -- -- ⁇ (CodeModule.C≡ c x y) = (x ⊓[ c ] y) ⊢ x ≅ y
-- -- -- -- -- ⁇ (CodeModule.Cμ tyCtor c D x) = {!!} --μ⁇

-- -- -- -- -- _⊓[_]_ x c y {reflp} with valueHead {c = c} x in eq1 | valueHead {c = c} y in eq2 |  headMatchView  (valueHead {c = c} x) (valueHead {c = c} y)
-- -- -- -- -- ... | h1 | h2 | H℧L x₁ = ℧ c
-- -- -- -- -- ... | h1 | h2 | H℧R x₁ = ℧ c
-- -- -- -- -- ... | H⁇ |  h2 |  H⁇L x₁ x₂ = y
-- -- -- -- -- ... | .(HStatic _) | H⁇ | H⁇R x₁ = x
-- -- -- -- -- ... | .(HStatic _) | .(HStatic _) | HNeq x₁ = ℧ c
-- -- -- -- -- (x ⊓[ CodeModule.C𝟙 ] y) {reflp} | .(HStatic _) | .(HStatic _) | HEq x₁ = x and y
-- -- -- -- -- (f ⊓[ CodeModule.CΠ dom cod ] g) {reflp} | .(HStatic _) | .(HStatic _) | HEq x₁ = λ x → {!!} -- ⦇ _⊓[ cod x ]_ (f x)  (g x) ⦈
-- -- -- -- -- ((x1 , y1) ⊓[ CodeModule.CΣ dom cod ] (x2 , y2)) {reflp} | .(HStatic _) | .(HStatic _) | HEq x₁ = (x1 ⊓[ dom ] x2) , (cast (cod x1) (cod _) y1 ⊓[ cod _ ] cast (cod x2) (cod _) y2)
-- -- -- -- -- ((w1 ⊢ x ≅ y) ⊓[ CodeModule.C≡ c x y ] (w2 ⊢ x ≅ y)) {reflp} | .(HStatic _) | .(HStatic _) | HEq x₁ = (w1 ⊓[ c ] w2) ⊢ x ≅ y
-- -- -- -- -- (x ⊓[ CodeModule.Cμ tyCtor c D x₂ ] y) {reflp} | .(HStatic _) | .(HStatic _) | HEq x₁ = {!!}
-- -- -- -- -- _⊓[_]_ {suc ℓ} x CodeModule.CType y {reflp} | .(HStatic _) | .(HStatic _) | HEq x₁ = codeMeet x y


-- -- -- -- -- -- Meet of elements at type ⁇
-- -- -- -- -- (CodeModule.⁇Π f ⊓[ CodeModule.C⁇ ] CodeModule.⁇Π g) {reflp} | HStatic HΠ | .(HStatic HΠ) | HEq reflp
-- -- -- -- --   = ⁇Π (λ x → ⦇ _⊓[ C⁇ ]_ (f x) (g x) ⦈)
-- -- -- -- -- (CodeModule.⁇Σ (x1 , y1) ⊓[ CodeModule.C⁇ ] CodeModule.⁇Σ (x2 , y2)) {reflp} | HStatic HΣ | .(HStatic HΣ) | HEq reflp
-- -- -- -- --   = ⁇Σ ((x1 ⊓[ C⁇ ] x2) , (y1 ⊓[ C⁇ ] y2))
-- -- -- -- -- (CodeModule.⁇≡ (x ⊢ _ ≅ _) ⊓[ CodeModule.C⁇ ] CodeModule.⁇≡ (y ⊢ _ ≅ _)) {reflp} | HStatic H≅ | .(HStatic H≅) | HEq reflp = ⁇≡ ((x ⊓[ C⁇ ] y) ⊢ _ ≅ _)
-- -- -- -- -- (CodeModule.⁇𝟙 ⊓[ CodeModule.C⁇ ] CodeModule.⁇𝟙) {reflp} | HStatic H⊤ | .(HStatic H⊤) | HEq reflp = ⁇𝟙
-- -- -- -- -- _⊓[_]_ {suc ℓ} (CodeModule.⁇Type x) CodeModule.C⁇ (CodeModule.⁇Type y) {reflp} | HStatic HType |  .(HStatic HType) | HEq reflp = ⁇Type {{inst = suc<}} (codeMeet x y)
-- -- -- -- -- (CodeModule.⁇μ tyCtor ctor x ⊓[ CodeModule.C⁇ ] CodeModule.⁇μ tyCtor₁ ctor₁ x₁) {reflp} | HStatic (HData tyCtor₂ x₂) | .(HStatic (HData tyCtor₂ x₂)) | HEq reflp = {!!}

-- -- -- -- -- codeMeet c1 c2 with codeHead c1 in eq1 | codeHead c2 in eq2 | headMatchView (codeHead c1) (codeHead c2)
-- -- -- -- -- ... | h1 | h2 | H℧L x = C℧
-- -- -- -- -- ... | h1 | h2 | H℧R x = C℧
-- -- -- -- -- ... | h1 | h2 | H⁇L x x₁ = c2
-- -- -- -- -- ... | .(HStatic _) | h2 | H⁇R x = c1
-- -- -- -- -- ... | .(HStatic _) | .(HStatic _) | HNeq x = C℧
-- -- -- -- -- codeMeet (CodeModule.CΠ dom1 cod1) (CodeModule.CΠ dom2 cod2) | HStatic HΠ | .(HStatic HΠ) | HEq reflp
-- -- -- -- --   = CΠ (codeMeet dom1 dom2) λ x → codeMeet (cod1 (cast (codeMeet dom1 dom2) dom1 x)) (cod2 (cast (codeMeet dom1 dom2) dom2 x))
-- -- -- -- -- codeMeet (CodeModule.CΣ dom1 cod1) (CodeModule.CΣ dom2 cod2) | HStatic HΣ | .(HStatic HΣ) | HEq reflp
-- -- -- -- --   = CΠ (codeMeet dom1 dom2) λ x → codeMeet (cod1 (cast (codeMeet dom1 dom2) dom1 x)) (cod2 (cast (codeMeet dom1 dom2) dom2 x))
-- -- -- -- -- codeMeet (CodeModule.C≡ c1 x1 y1) (CodeModule.C≡ c2 x2 y2) | HStatic H≅ | .(HStatic H≅) | HEq reflp
-- -- -- -- --   = C≡ c12 (cast c1 c12 x1 ⊓[ c12 ] cast c2 c12 x2) (cast c1 c12 y1 ⊓[ c12 ] cast c2 c12 y2)
-- -- -- -- --     where
-- -- -- -- --       c12 = codeMeet c1 c2
-- -- -- -- -- codeMeet CodeModule.C𝟙 CodeModule.C𝟙 | HStatic H⊤ | .(HStatic H⊤) | HEq reflp = C𝟙
-- -- -- -- -- codeMeet CodeModule.C𝟘 CodeModule.C𝟘 | HStatic H⊥ | .(HStatic H⊥) | HEq reflp = C𝟘
-- -- -- -- -- codeMeet (CodeModule.CType {{inst = inst}}) CodeModule.CType | HStatic HType | .(HStatic HType) | HEq reflp = CType {{inst = inst}}
-- -- -- -- -- codeMeet (CodeModule.Cμ tyCtor c1 D x) (CodeModule.Cμ tyCtor₁ c2 D₁ x₁) | HStatic (HCtor x₂) | .(HStatic (HCtor x₂)) | HEq reflp = {!!}

-- -- -- -- -- toGerm (CodeModule.CΠ dom cod) HΠ p f = λ x → {!!} -- ⦇ (cast (cod (cast C⁇ dom x)) C⁇) (f (cast C⁇ dom x)) ⦈
-- -- -- -- -- toGerm (CodeModule.CΣ dom cod) HΣ p (x , y) = cast dom C⁇ x , cast (cod x) C⁇ y
-- -- -- -- -- toGerm (CodeModule.C≡ c x₁ y) H≅ p (wit ⊢ _ ≅ _) = cast c C⁇ wit ⊢ _ ≅ _
-- -- -- -- -- toGerm CodeModule.C𝟙 H⊤ p x = x
-- -- -- -- -- toGerm CodeModule.C𝟘 H⊥ p x = x
-- -- -- -- -- toGerm {suc ℓ} CodeModule.CType HType p x = x
-- -- -- -- -- toGerm (CodeModule.Cμ tyCtor c D x₁) (HCtor x₂) p x = {!!}

-- -- -- -- -- fromGerm c h p x = {!!}
