{-# OPTIONS --cubical --guarded --lossy-unification #-}
-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
-- open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.Data.FinData
-- open import Cubical.Data.Equality
open import Cubical.Data.Sigma
open import UnkGerm
open import GuardedAlgebra
open import Cubical.Induction.WellFounded
open import Cubical.Foundations.Prelude
-- open import Cubical.Data.Equality using (ptoc)
open import Cubical.HITs.PropositionalTruncation as Prop

open import ApproxExact
open import GTypes
open import Code
open import Cubical.Foundations.Transport

module Sizes.NatLim {{_ : DataTypes}} {{_ : DataGerms}} where


open import Sizes.Size

_+ₛ_ : Size → ℕ → Size
s +ₛ ℕ.zero = s
s +ₛ (ℕ.suc n) = S↑ (s +ₛ n)

+↑dist : ∀ {s n} → S↑ (s +ₛ n) ≡c (S↑ s) +ₛ n
+↑dist {n = ℕ.zero} = reflc
+↑dist {n = ℕ.suc n} = congPath S↑ +↑dist 

+-mono : ∀ {s1 s2 n} → s1 ≤ₛ s2 → (s1 +ₛ n) ≤ₛ (s2 +ₛ n)
+-mono {n = ℕ.zero} lt = lt
+-mono {n = ℕ.suc n} lt = ≤ₛ-sucMono (+-mono lt)

abstract
  ℕLim : (ℕ → Size) → Size
  ℕLim f = SLim (Cℕ {ℓ = 0}) (λ arrows → SLim (Cℕ {ℓ = 0}) λ n → f (CℕtoNat n) +ₛ (CℕtoNat arrows))


{-# INJECTIVE ℕLim #-}

abstract
    ℕLim-cocone : ∀ {f : ℕ → Size} n → f n ≤ₛ ℕLim f
    ℕLim-cocone {f = f} n = substPath (λ x → f n ≤ₛ f x) (sym (Cℕembed n)) ≤ₛ-refl ≤⨟ ≤ₛ-cocone GZero ≤⨟ ≤ₛ-extLim λ k → ≤ₛ-cocone (CℕfromNat n)

    ℕLim-wrapL : ∀ {s : Size} → s ≤ₛ ℕLim (λ _ → s)
    ℕLim-wrapL = ℕLim-cocone 0

    ℕLim-extSuc : ∀ {f g : ℕ → Size} → (∀ {n} → f n ≤ₛ g (ℕ.suc n)) → ℕLim f ≤ₛ ℕLim g
    ℕLim-extSuc lt = ≤ₛ-extLim λ _ → ≤ₛ-limiting (λ kn →  +-mono lt ≤⨟ ≤ₛ-cocone (GSuc kn)  )

    ℕLim-ext : ∀ {f g : ℕ → Size} → (∀ {n} → f n ≤ₛ g n) → ℕLim f ≤ₛ ℕLim g
    ℕLim-ext lt = ≤ₛ-extLim λ _ → ≤ₛ-limiting (λ kn →  ≤ₛ-cocone kn ≤⨟ ≤ₛ-extLim λ k → +-mono lt )

    ℕLim-extExists : {f g : ℕ → Size} → (∀ n → Σ[ n' ∈ ℕ ]( f n ≤ₛ g n' )) → ℕLim f ≤ₛ ℕLim g
    ℕLim-extExists {g = g} lt = ≤ₛ-extLim (λ fuel →
      ≤ₛ-limiting λ kn → +-mono (snd (lt (CℕtoNat kn)))
      ≤⨟  +-mono (substPath (λ x → g x ≤ₛ g (CℕtoNat (CℕfromNat (fst (lt (CℕtoNat kn)))))) (Cℕembed (fst (lt (CℕtoNat kn)))) ≤ₛ-refl)
      ≤⨟ ≤ₛ-cocone (CℕfromNat (fst (lt (CℕtoNat kn)))))

    ℕLim-extR : ∀ {s} {f : ℕ → Size} → (∀ {n} → S↑ s ≤ₛ f n) → S↑ s ≤ₛ ℕLim f
    ℕLim-extR lt = ℕLim-wrapL ≤⨟ ℕLim-ext lt

    ℕsucMono : ∀ {f : ℕ → Size} {s : Size} → (∀ {n} → s ≤ₛ f n) → S↑ s ≤ₛ ℕLim (λ n → S↑ (f n))
    ℕsucMono {s = s} lt = ℕLim-cocone 0 ≤⨟ ℕLim-ext {f = λ _ → S↑ s} (≤ₛ-sucMono lt)


    ℕmaxL : ∀ {s} {f : ℕ → Size} → smax s (ℕLim λ n → (f n)) ≤ₛ ℕLim λ n → smax s (f n)
    ℕmaxL = smax-lub (ℕLim-wrapL ≤⨟ ℕLim-ext smax-≤L) (ℕLim-ext smax-≤R)

    ℕmaxR : ∀ {s} {f : ℕ → Size} → smax (ℕLim λ n → f n) s ≤ₛ ℕLim λ n → smax (f n) s
    ℕmaxR = smax-lub (ℕLim-ext smax-≤L) (ℕLim-wrapL ≤⨟ ℕLim-ext smax-≤R)

    ℕLim-absorb : ∀ {f : ℕ → Size} → ℕLim (λ n → S↑ (f n)) ≤ₛ ℕLim f
    ℕLim-absorb {f = f} = ≤ₛ-extExists λ n1 → GSuc n1 , ≤ₛ-extLim λ k → substPath (λ x → x ≤ₛ S↑ (f (CℕtoNat k) +ₛ CℕtoNat n1)) +↑dist ≤ₛ-refl

    -- ℕLim-sucMono : ∀ {f : ℕ → Size} → S↑ (ℕLim f) ≤ₛ ℕLim (λ n → S↑ (f n))
    -- ℕLim-sucMono = {!!}



abstract
    CFin : ∀ (n : ℕ) → ℂ 0
    CFin ℕ.zero = C℧
    CFin (ℕ.suc n) = CΣ C𝟙 (λ {℧𝟙  → C℧ ; Gtt → CFin n})


    fromCFin : ∀ {n} → El {{æ = Approx}} (CFin n) → Fin (ℕ.suc n)
    fromCFin {ℕ.zero} _ = Fin.zero
    fromCFin {ℕ.suc n} (℧𝟙 , rest) = Fin.zero
    fromCFin {ℕ.suc n} (Gtt , rest) = Fin.suc (fromCFin rest)


    toCFin : ∀ {n} → Fin (ℕ.suc n) → El {{æ = Approx}} (CFin n)
    toCFin {n = ℕ.zero} x = ℧𝟘
    toCFin {n = ℕ.suc n} Fin.zero = ℧𝟙 , ℧𝟘
    toCFin {n = ℕ.suc n} (Fin.suc x) = Gtt , toCFin x

    fromToCFin : ∀ {n} (x : Fin (ℕ.suc n)) → fromCFin (toCFin x) ≡p x
    fromToCFin {ℕ.zero} Fin.zero = reflp
    fromToCFin {ℕ.suc n} Fin.zero = reflp
    fromToCFin {ℕ.suc n} (Fin.suc x) rewrite fromToCFin x = reflp




    FinLim : ∀ {n} → (Fin n → Size) → Size
    FinLim {ℕ.zero} f = SZ
    FinLim {ℕ.suc n} f = SLim (CFin n) (λ x → f (fromCFin x))


    DLim : ∀ (tyCtor : CName) → ((d : DName tyCtor) → Size) → Size
    DLim tyCtor f = FinLim f

    FinLim-cocone : ∀ {n} → (f : ( Fin n) → Size) → (d : Fin n) → f d ≤ₛ FinLim f
    FinLim-cocone {ℕ.suc n} f d = pSubst (λ x → f d ≤ₛ f x) (pSym (fromToCFin d)) ≤ₛ-refl ≤⨟ ≤ₛ-cocone (toCFin d)

    extFinLim : ∀ {n} → (f1 f2 : (d : Fin n) → Size) → (∀ d → f1 d ≤ₛ f2 d) → (FinLim f1) ≤ₛ (FinLim f2)
    extFinLim {n = ℕ.zero} f1 f2 lt = ≤ₛ-Z
    extFinLim  {ℕ.suc n} f1 f2 lt = ≤ₛ-extLim  (λ k → lt (fromCFin k))

    smax-FinLim2 : ∀ {n} → (f1 f2 : (d : Fin n) → Size) →  FinLim (λ d1 → FinLim (λ d2 → smax (f1 d1) (f2 d2))) ≤ₛ smax (FinLim f1) (FinLim f2)
    smax-FinLim2 {ℕ.zero} f1 f2 = ≤ₛ-Z
    smax-FinLim2 {ℕ.suc n} f1 f2 = smax-lim2L (λ z → f1 (fromCFin z)) (λ z → f2 (fromCFin z))
