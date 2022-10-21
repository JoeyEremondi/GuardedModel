

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
open import Cubical.Data.Equality
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Inductives
open import GuardedAlgebra
open import Cubical.Induction.WellFounded
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Equality using (ptoc)

open import ApproxExact

-- open import InductiveCodes
open import Cubical.Foundations.Transport


-- Brouwer Tree ordinals
-- Based on the presentation by Kraus, Forsburg and Xu
-- https://arxiv.org/abs/2104.02549

-- The main difference is that we allow the limit over the elements of any code type, not just natural numbers

open import InductiveCodes
module CodePair {{dt : DataTypes}} {{dg : DataGerms}} {{ic : InductiveCodes }} where






open import Code
open import WMuEq
open import Head
open import Util

open import Ord {{dt}} {{dg}} -- ℂ El ℧ C𝟙 refl
open import CodeSize {{dt}} {{dg}} {{ic}}


record CodePairSize {ℓ} (c1 c2 : ℂ ℓ) : Set where
  constructor CPSize
  field
    csize : Ord
    {{pairIsSuc}} : IsSucO csize
    ltL : codeSize c1 ≤o csize
    ltR : codeSize c2 ≤o csize

open CodePairSize public


codePairSize : ∀ {ℓ h1 h2} → (c1 c2 : ℂ ℓ)
  → {@(tactic default (headMatchView (codeHead c1) (codeHead c2))) view : HeadMatchView h1 h2}
  → {@(tactic default (reflp {x = codeHead c1})) eq1 : h1 ≡p codeHead c1}
  → {@(tactic default (reflp {x = codeHead c2})) eq2 : h2 ≡p codeHead c2}
  → CodePairSize c1 c2
descPairSize : ∀ {ℓ sig} →  {cI cB cI' cB' : ℂ ℓ} → (D1 : ℂDesc cI cB sig) (D2 : ℂDesc cI' cB' sig) → Σ[ o ∈ Ord ]( descSize D1 ≤o o × descSize D2 ≤o o )

codePairSize c1 c2 {H℧L reflp}  with C℧ ← c1 = CPSize (codeSize c2) {{codeIsSuc}} codeSuc (≤o-refl _)
codePairSize c1 c2 {H℧R reflp}  with C℧ ← c2 = CPSize (codeSize c1) {{codeIsSuc}} (≤o-refl _) (codeSuc)
codePairSize c1 c2 {H⁇L reflp x₁}  with C⁇ ← c1 = CPSize (codeSize c2) {{codeIsSuc}} (codeSuc) (≤o-refl _)
codePairSize c1 c2 {H⁇R reflp}  with C⁇ ← c2 = CPSize (codeSize c1) {{codeIsSuc}} (≤o-refl _) (codeSuc)
codePairSize c1 c2 {HNeq x}  =  CPSize ((smax (codeSize c1) (codeSize c2) {{codeIsSuc}} {{codeIsSuc}})) {{smaxIsSuc {{codeIsSuc}} {{codeIsSuc}}}} (smax-≤L {{codeIsSuc}} {{codeIsSuc}}) (smax-≤R {{codeIsSuc}} {{codeIsSuc}})
codePairSize (CΠ dom1 cod1) (CΠ dom2 cod2) {HEq {h1 = HΠ} reflp}
  = CPSize
      (O↑ (omax (csize (codePairSize dom1 dom2)) (OLim {{æ = Approx}} dom1 λ x1 → OLim {{æ = Approx}} dom2 λ x2 → csize (codePairSize (cod1 x1) (cod2 x2)))))
      (≤o-sucMono (omax-mono (ltL (codePairSize dom1 dom2)) (extLim {{æ = Approx}} _ _
        (λ k → ≤o-℧ {{æ = Approx}} (ltL (codePairSize (cod1 k) (cod2 _)))) )))
      (≤o-sucMono (omax-mono (ltR (codePairSize dom1 dom2)) (≤o-℧ {{æ = Approx}} (extLim ⦃ æ = Approx ⦄ _ _
        λ k → ltR (codePairSize (cod1 (℧Approx dom1)) (cod2 k))))))
codePairSize (CΣ dom1 cod1) (CΣ dom2 cod2) {HEq {h1 = HΣ} reflp}
  = CPSize
      (O↑ (omax (csize (codePairSize dom1 dom2)) (OLim {{æ = Approx}} dom1 λ x1 → OLim {{æ = Approx}} dom2 λ x2 → csize (codePairSize (cod1 x1) (cod2 x2)))))
      (≤o-sucMono (omax-mono (ltL (codePairSize dom1 dom2)) (extLim {{æ = Approx}} _ _
        (λ k → ≤o-℧ {{æ = Approx}} (ltL (codePairSize (cod1 k) (cod2 _)))) )))
      (≤o-sucMono (omax-mono (ltR (codePairSize dom1 dom2)) (≤o-℧ {{æ = Approx}} (extLim ⦃ æ = Approx ⦄ _ _
        λ k → ltR (codePairSize (cod1 (℧Approx dom1)) (cod2 k))))))
codePairSize (C≡ c1 x1 y1) (C≡ c2 x2 y2) {HEq {h1 = H≅} reflp}
  = CPSize
    (O↑ (omax (csize rrec) (omax (omax (elSize {{æ = Approx}} c1 x1) (elSize {{Approx}} c1 y1)) (omax (elSize {{Approx}} c2 x2) (elSize {{Approx}} c2 y2)))))
    (≤o-sucMono (omax-mono (ltL rrec) omax-≤L))
    (≤o-sucMono (omax-mono (ltR rrec) omax-≤R))
    where
      rrec = codePairSize c1 c2
codePairSize C𝟙 C𝟙 {HEq {h1 = H𝟙} reflp} = CPSize O1 (≤o-refl _) (≤o-refl _)
codePairSize C𝟘 C𝟘 {HEq {h1 = H𝟘} reflp} = CPSize O1 (≤o-refl _) (≤o-refl _)
codePairSize CType CType {HEq {h1 = HType} reflp} = CPSize O1 (≤o-refl _) (≤o-refl _)
codePairSize (Cμ tyCtor c1 D1 i) (Cμ _ c2 D2 i2) {HEq {h1 = HCtor x₂} reflp} {reflp} {reflp}
  = CPSize (O↑ (DLim tyCtor (λ d → fst (descPairSize (D1 d) (D2 d)))))
    (≤o-sucMono (extDLim tyCtor _ _ (λ d → fst (snd (descPairSize (D1 d) (D2 d))))))
    (≤o-sucMono (extDLim tyCtor _ _ (λ d → snd (snd (descPairSize (D1 d) (D2 d))))))

descPairSize {cB = cB} {cB' = cB'} (CEnd i) (CEnd i₁) = O↑ (omax (elSize ⦃ Approx ⦄ _ i) (elSize {{Approx}} _ i₁)) , ≤o-sucMono omax-≤L , ≤o-sucMono omax-≤R
descPairSize {cB = cB} {cB' = cB'} (CArg c1 D1) (CArg c2 D2) =
  O↑ (omax (OLim ⦃ æ = Approx ⦄ cB λ b → OLim {{æ = Approx}} cB' λ b' →  csize (codePairSize (c1 b) (c2 b'))) (fst (descPairSize D1 D2)))
  , ≤o-sucMono (omax-mono (extLim ⦃ æ = Approx ⦄ _ _ λ k → ≤o-℧ ⦃ æ = Approx ⦄ (ltL (codePairSize _ _))) (fst (snd (descPairSize D1 D2))))
  ,  ≤o-sucMono (omax-mono (≤o-℧ ⦃ æ = Approx ⦄ (extLim ⦃ æ = Approx ⦄ _ _ (λ k → ltR (codePairSize (c1 _) (c2 _))))) (snd (snd (descPairSize D1 D2))))
descPairSize {cI = cI} {cB = cB} {cI' = cI'} {cB' = cB'} (CRec j1 D1) (CRec j2 D2) =
  O↑ (omax (fst (descPairSize D1 D2)) (omax (elSize ⦃ Approx ⦄ cI j1) (elSize {{Approx}} cI' j2)))
  , ≤o-sucMono (omax-mono (fst (snd (descPairSize D1 D2))) omax-≤L)
  , ≤o-sucMono (omax-mono (snd (snd (descPairSize D1 D2))) omax-≤R)
descPairSize {cI = cI} {cB = cB} {cI' = cI'} {cB' = cB'} (CHRec c1 j1 D1) (CHRec c2 j2 D2) =
  O↑
    (omax
      (OLim {{æ = Approx}} cB λ b → OLim {{æ = Approx}} cB' λ b' → OLim {{æ = Approx}} (c1 b) λ a → OLim {{æ = Approx}}(c2 b') λ a' →
        omax (elSize ⦃ Approx ⦄ cI (j1 b a)) (elSize {{Approx}} cI' (j2 b' a')))
      (fst (descPairSize D1 D2)))
  , ≤o-sucMono (omax-mono (extLim ⦃ æ = Approx ⦄ _ _ λ b → ≤o-℧ ⦃ æ = Approx ⦄ (extLim ⦃ æ = Approx ⦄ _ _ (λ a →  ≤o-℧ {{æ = Approx}} omax-≤L))) (fst (snd (descPairSize D1 D2))))
  , ≤o-sucMono (omax-mono (≤o-℧ ⦃ æ = Approx ⦄ (extLim ⦃ æ = Approx ⦄ _ _ (λ a' → ≤o-℧ {{æ = Approx}} (extLim ⦃ æ = Approx ⦄ _ _ (λ k → omax-≤R))))) (snd (snd (descPairSize D1 D2))))


codePairSizeCommut : ∀ {ℓ h1 h2} → (c1 c2 : ℂ ℓ)
  → {@(tactic default (headMatchView (codeHead c1) (codeHead c2))) view : HeadMatchView h1 h2}
  → {@(tactic default (headMatchView (codeHead c2) (codeHead c1))) view2 : HeadMatchView h2 h1}
  → {@(tactic default (reflp {x = codeHead c1})) eq1 : h1 ≡p codeHead c1}
  → {@(tactic default (reflp {x = codeHead c2})) eq2 : h2 ≡p codeHead c2}
  → csize (codePairSize c1 c2 {view} {eq1} {eq2} ) ≤o csize (codePairSize c2 c1 {view2} {eq2} {eq1})
codePairSizeCommut c1 c2 {H℧L reflp} {H℧L reflp} {eq1} {eq2} with C℧ ← c1 | C℧ ← c2  = ≤o-refl _
codePairSizeCommut c1 c2 {H℧L reflp} {H℧R reflp} {eq1} {eq2} with C℧ ← c1  = ≤o-refl _
codePairSizeCommut c1 c2 {H℧L reflp} {H⁇L reflp x₁} {eq1} {eq2} with () ← x₁ reflp
codePairSizeCommut c1 c2 {H℧R reflp} {H℧L reflp} {eq1} {eq2} with  C℧ ← c2  = ≤o-refl _
codePairSizeCommut c1 c2 {H℧R reflp} {H℧R reflp} {eq1} {eq2} with C℧ ← c1 | C℧ ← c2  = ≤o-refl _
codePairSizeCommut {_} {_} {H⁇} c1 c2 {H⁇L reflp x₁} {H⁇L reflp x₂} {eq1} {eq2} with C⁇ ← c1 | C⁇ ← c2 = ≤o-refl _
codePairSizeCommut {h2 = H℧} c1 c2 {H⁇L reflp x₁} {view2} {eq1} {eq2} with () ← x₁ reflp
codePairSizeCommut {_} {_} {HStatic x} c1 c2 {H⁇L reflp x₁} {H⁇R reflp} {eq1} {eq2} with C⁇ ← c1 = ≤o-refl _
codePairSizeCommut c1 c2 {H⁇R reflp} {H⁇L reflp x₁} {eq1} {eq2} with C⁇ ← c2 = ≤o-refl _
codePairSizeCommut c1 c2 {HNeq x₁} {HEq reflp} {eq1} {eq2} with () ← x₁ reflp
codePairSizeCommut c1 c2 {HEq reflp} {HNeq x₁} {eq1} {eq2} with () ← x₁ reflp
codePairSizeCommut c1 c2 {HNeq x} {HNeq x₁} {eq1} {eq2} = smax-commut {{codeIsSuc}} {{codeIsSuc}}
codePairSizeCommut c1 c2 {HEq reflp} {HEq pf} {eq1} {eq2} rewrite decUIP headDecEq pf reflp = helper c1 c2 eq1 eq2
  where
    helper : ∀ {ℓ} {h} → (c1 c2 : ℂ ℓ) → (eq1 : HStatic h ≡p codeHead c1) → (eq2 : HStatic h ≡p codeHead c2)
      → csize (codePairSize c1 c2 {HEq reflp} {eq1} {eq2} ) ≤o csize (codePairSize c2 c1 {HEq reflp} {eq2} {eq1})
    helper {h = HΠ} (CodeModule.CΠ dom1 cod1) (CodeModule.CΠ dom2 cod2) eq1 eq2
      = ≤o-sucMono
        (omax-mono
          (codePairSizeCommut dom1 dom2)
          (≤o-limiting ⦃ æ = Approx ⦄ _ (λ k1 → extLim ⦃ æ = Approx ⦄ _ _ (λ k2 →
            ≤o-cocone ⦃ æ = Approx ⦄ _ k1 (codePairSizeCommut (cod1 k1) (cod2 k2))))))
    helper {h = HΣ} (CodeModule.CΣ dom1 cod1) (CodeModule.CΣ dom2 cod2) eq1 eq2
      = ≤o-sucMono
        (omax-mono
          (codePairSizeCommut dom1 dom2)
          (≤o-limiting ⦃ æ = Approx ⦄ _ (λ k1 → extLim ⦃ æ = Approx ⦄ _ _ (λ k2 →
            ≤o-cocone ⦃ æ = Approx ⦄ _ k1 (codePairSizeCommut (cod1 k1) (cod2 k2))))))
    helper {h = H≅} (CodeModule.C≡ c1 x y) (CodeModule.C≡ c2 x₁ y₁) eq1 eq2
      = ≤o-sucMono (omax-mono
        (codePairSizeCommut c1 c2)
        omax-commut)
    helper {h = H𝟙} CodeModule.C𝟙 CodeModule.C𝟙 eq1 eq2 = ≤o-refl _
    helper {h = H𝟘} CodeModule.C𝟘 CodeModule.C𝟘 eq1 eq2 = ≤o-refl _
    helper {h = HType} CodeModule.CType CodeModule.CType eq1 eq2 = ≤o-refl _
    helper {h = HCtor x} (CodeModule.Cμ tyCtor c1 D1 x₁) (CodeModule.Cμ tyCtor₁ c2 D2 x₂) reflp reflp
      = ≤o-sucMono (extDLim x _ _ (λ d → helperDesc (D1 d) (D2 d)))
      where
        helperDesc : ∀ {ℓ sig} →  {cI cB cI' cB' : ℂ ℓ} → (D1 : ℂDesc cI cB sig) (D2 : ℂDesc cI' cB' sig) → fst (descPairSize D1 D2) ≤o fst (descPairSize D2 D1)
        helperDesc (CodeModule.CEnd i) (CodeModule.CEnd i₁) = ≤o-sucMono omax-commut
        helperDesc (CodeModule.CArg c D1) (CodeModule.CArg c₁ D2)
          = ≤o-sucMono (omax-mono
              (≤o-limiting ⦃ æ = Approx ⦄ _ (λ k → extLim {{æ = Approx}} _ _ λ k' →
                ≤o-cocone ⦃ æ = Approx ⦄ _ k (codePairSizeCommut (c k) (c₁ k'))))
              (helperDesc D1 D2)
              )
        helperDesc (CodeModule.CRec j D1) (CodeModule.CRec j₁ D2)
          = ≤o-sucMono (omax-mono
            (helperDesc D1 D2)
            omax-commut)
        helperDesc (CodeModule.CHRec c j D1) (CodeModule.CHRec c₁ j₁ D2)
          = ≤o-sucMono (omax-mono
            (≤o-limiting ⦃ æ = Approx ⦄ _ (λ b → extLim {{æ = Approx}} _ _ λ b' →
                ≤o-cocone ⦃ æ = Approx ⦄ _ b (≤o-limiting ⦃ æ = Approx ⦄ _ (λ a → extLim {{æ = Approx}} _ _ λ a' →
                  ≤o-cocone ⦃ æ = Approx ⦄ _ a omax-commut))))
            (helperDesc D1 D2))

codeSize2 : ∀ {ℓ} → ℂ ℓ → ℂ ℓ → Ord
codeSize2 c1 c2 = csize (codePairSize c1 c2)

codeSize2≤ : ∀ {ℓ} (c1 c2 : ℂ ℓ) → omax (codeSize c1) (codeSize c2) ≤o codeSize2 c1 c2
codeSize2≤ c1 c2 = omax-LUB (ltL (codePairSize c1 c2)) (ltR (codePairSize c1 c2))


codePairAbsorb : ∀ {ℓ h1 h2} → (c1 c2 : ℂ ℓ)
  → {@(tactic default (headMatchView (codeHead c1) (codeHead c2))) view12 : HeadMatchView h1 h2}
  → {@(tactic default (reflp {x = codeHead c1})) eq1 : h1 ≡p codeHead c1}
  → {@(tactic default (reflp {x = codeHead c2})) eq2 : h2 ≡p codeHead c2}
  → codeSize c1 ≤o codeSize c2
  → csize (codePairSize c1 c2 {view12} {eq1} {eq2} ) ≤o codeSize c2
codePairAbsorb c1 c2 {H℧L reflp} {eq1} {eq2} lt with C℧ ← c1 = ≤o-refl _
codePairAbsorb c1 c2 {H℧R reflp} {eq1} {eq2} lt with C℧ ← c2 = lt
codePairAbsorb c1 c2 {H⁇L reflp x₁} {eq1} {eq2} lt with C⁇ ← c1 = ≤o-refl _
codePairAbsorb c1 c2 {H⁇R reflp} {eq1} {eq2} lt with C⁇ ← c2 = lt
codePairAbsorb c1 c2 {HNeq x} {eq1} {eq2} lt = smax-LUB ⦃ codeIsSuc ⦄ ⦃ codeIsSuc ⦄ ⦃ codeIsSuc ⦄ lt (≤o-refl _)
codePairAbsorb (CodeModule.CΠ dom1 cod1) (CodeModule.CΠ dom2 cod2) {HEq {h1 = HΠ} reflp} {eq1} {eq2} (≤o-sucMono lt) = ≤o-sucMono {!!}
codePairAbsorb (CodeModule.CΣ c1 cod) (CodeModule.CΣ c2 cod₁) {HEq {h1 = HΣ} reflp} {eq1} {eq2} lt = {!!}
codePairAbsorb (CodeModule.C≡ c1 x y) (CodeModule.C≡ c2 x₁ y₁) {HEq {h1 = H≅} reflp} {eq1} {eq2} lt = {!!}
codePairAbsorb CodeModule.C𝟙 CodeModule.C𝟙 {HEq {h1 = H𝟙} reflp} {eq1} {eq2} lt = {!!}
codePairAbsorb CodeModule.C𝟘 CodeModule.C𝟘 {HEq {h1 = H𝟘} reflp} {eq1} {eq2} lt = {!!}
codePairAbsorb CodeModule.CType CodeModule.CType {HEq {h1 = HType} reflp} {eq1} {eq2} lt = {!!}
codePairAbsorb (CodeModule.Cμ tyCtor c1 D x) (CodeModule.Cμ tyCtor₁ c2 D₁ x₁) {HEq {h1 = HCtor x₂} reflp} {eq1} {eq2} lt = {!!}

codePairLUB : ∀ {ℓ h h1 h2} → (c c1 c2 : ℂ ℓ)
  → {@(tactic default (headMatchView (codeHead c1) (codeHead c2))) view12 : HeadMatchView h1 h2}
  → {@(tactic default (headMatchView (codeHead c) (codeHead c2))) view : HeadMatchView h h2}
  → {@(tactic default (reflp {x = codeHead c1})) eq : h ≡p codeHead c}
  → {@(tactic default (reflp {x = codeHead c1})) eq1 : h1 ≡p codeHead c1}
  → {@(tactic default (reflp {x = codeHead c2})) eq2 : h2 ≡p codeHead c2}
  → codeSize c ≤o csize (codePairSize c1 c2 {view12} {eq1} {eq2})
  → csize (codePairSize c c2 {view} {eq} {eq2} ) ≤o csize (codePairSize c1 c2 {view12} {eq1} {eq2})
codePairLUB c c1 c2 {view12} {H℧L reflp} {eq} {eq1} {eq2} lt with C℧ ← c = ltR (codePairSize c1 c2 {view12} {eq1} {eq2})
codePairLUB c c1 c2 {H℧L reflp} {H℧R reflp} {eq} {eq1} {eq2} lt with C℧ ← c2 with C℧ ← c1 = lt
codePairLUB c c1 c2 {H℧R reflp} {H℧R reflp} {eq} {eq1} {eq2} lt with C℧ ← c2 = lt
codePairLUB c c1 c2 {H⁇L x x₁} {H℧R reflp} {eq} {eq1} {eq2} lt with C℧ ← c2 with () ← x₁ reflp
codePairLUB c c1 c2 {view12} {H⁇L reflp x₁} {eq} {eq1} {eq2} lt with C⁇ ← c = ltR (codePairSize c1 c2 {view12} {eq1} {eq2})
codePairLUB c c1 c2 {H℧L reflp} {H⁇R reflp} {eq} {eq1} {eq2} lt with C⁇ ← c2 with C℧ ← c1 = lt
codePairLUB c c1 c2 {H⁇L reflp x₁} {H⁇R reflp} {eq} {eq1} {eq2} lt with C⁇ ← c2 with C⁇ ← c1 = lt
codePairLUB c c1 c2 {H⁇R reflp} {H⁇R reflp} {eq} {eq1} {eq2} lt with C⁇ ← c2 = lt
codePairLUB c c1 c2 {view12} {HNeq x} {eq} {eq1} {eq2} lt = smax-LUB ⦃ codeIsSuc ⦄ ⦃ codeIsSuc ⦄ ⦃ pairIsSuc (codePairSize c1 c2 {view12} {eq1} {eq2}) ⦄ lt (ltR (codePairSize c1 c2 {view12} {eq1} {eq2}))
codePairLUB c c1 c2 {H℧L reflp} {HEq reflp} {eq} {eq1} {eq2} lt with C℧ ← c1 = {!lt!}
codePairLUB c c1 c2 {H⁇L reflp x₁} {HEq reflp} {eq} {eq1} {eq2} lt with C⁇ ← c1 = {!!}
codePairLUB c c1 c2 {HNeq x} {HEq reflp} {eq} {eq1} {eq2} lt = {!!}
codePairLUB c c1 c2 {HEq reflp} {HEq reflp} {eq} {eq1} {eq2} lt = {!!}
