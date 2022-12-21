
open import UnkGerm
open import InductiveCodes
module Sizes.MultiMax {{_ : DataTypes}} {{_ : DataGerms}} where

open import Sizes.Size

open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.FinData

abstract
  smax* : ∀ {n} → Vec Size n → Size
  smax* [] = SZ
  smax* (x ∷ os) = smax x (smax* os)

  smax*-≤L : ∀ {n o} {os : Vec Size n} → o ≤ₛ smax* (o ∷ os)
  smax*-≤L {o = o} {os = os} = smax-≤L {s1 = o} {s2 = smax* os}

  smax*-≤R : ∀ {n o} {os : Vec Size n} → smax* os ≤ₛ smax* (o ∷ os)
  smax*-≤R {o = o} {os = os} = smax-≤R {s1 = o} {s2 = smax* os}

  smax*-≤-n : ∀ {n} {os : Vec Size n} (f : Fin n) → lookup f os ≤ₛ smax* os
  smax*-≤-n {os = o ∷ os} Fin.zero = smax*-≤L {o = o} {os = os}
  smax*-≤-n {os = o ∷ os} (Fin.suc f) = smax*-≤-n f ≤⨟ (smax*-≤R {o = o} {os = os})
  -- smax*-≤-n f ≤⨟ (smax*-≤R {o = o} {os = os})

  smax*-swap : ∀ {n} {os1 os2 : Vec Size n} → smax* (zipWith smax os1 os2) ≤ₛ smax (smax* os1) (smax* os2)
  smax*-swap {n = ℕ.zero} {[]} {[]} = ≤ₛ-Z
  smax*-swap {n = ℕ.suc n} {o1 ∷ os1} {o2 ∷ os2} =
    smax-monoR (smax*-swap {n = n}) ≤⨟ smax-swap4
    -- smax-monoR {s1 = smax o1 o2} (smax*-swap {n = n}) ≤⨟ smax-swap4 {o1 = o1} {o1' = o2} {o2 = smax* os1} {o2' = smax* os2}

  smax*-mono : ∀ {n} {os1 os2 : Vec Size n} → foldr (λ (o1 , o2) rest → (o1 ≤ₛ o2) × rest) Unit (zipWith _,_ os1 os2) → smax* os1 ≤ₛ smax* os2
  smax*-mono {ℕ.zero} {[]} {[]} lt = ≤ₛ-Z
  smax*-mono {ℕ.suc n} {o1 ∷ os1} {o2 ∷ os2} (lt , rest) = smax-mono {s1 = o1} {s1' = o2} lt (smax*-mono {os1 = os1} {os2 = os2} rest)

  smax*-monoR :  ∀ {n o} {os1 os2 : Vec Size n} → smax* os1 ≤ₛ smax* os2 → smax* (o ∷ os1) ≤ₛ smax* (o ∷ os2)
  smax*-monoL :  ∀ {n o1 o2} {os : Vec Size n} → o1 ≤ₛ o2 → smax* (o1 ∷ os) ≤ₛ smax* (o2 ∷ os)

  smax*-monoR lt = smax-monoR lt
  smax*-monoL lt = smax-monoL lt

  smax*-consL :  ∀ {n o} {os : Vec Size n} → smax* (o ∷ os) ≤ₛ smax o (smax* os)
  smax*-consL = smax-lub smax-≤L smax-≤R


  smax*-consR :  ∀ {n o} {os : Vec Size n} → smax o (smax* os) ≤ₛ  smax* (o ∷ os)
  smax*-consR = ≤ₛ-refl
