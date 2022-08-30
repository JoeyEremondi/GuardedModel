{-# OPTIONS --cubical --guarded #-}

-- open import Guarded
open import Cubical.Data.Maybe
open import Level
open import Cubical.Relation.Nullary
open import Cubical.Data.Equality using (_≡p_ ; reflp ; cong)
open import DecPEq
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.FinData
open import Cubical.Data.Equality
open import Cubical.Data.Sigma
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Prelude
open import Inductives
open import GuardedAlgebra
open import ApproxExact

module Head {{_ : DataTypes}} {{_ : DataGerms}} where

open import Code

data TyHead : Set where
  HΠ : TyHead
  HΣ : TyHead
  H≅ : TyHead
  H𝟙 : TyHead
  H𝟘 : TyHead
  HType : TyHead
  HCumul : TyHead
  HCtor : CName → TyHead

data GHead : Set where
  H⁇ : GHead
  H℧ : GHead
  HStatic : TyHead → GHead

valueHeadType : TyHead → Set
data ValHead : (h : GHead) → Set

valueHeadType ( HΠ) = Unit
valueHeadType ( HΣ) = Unit
valueHeadType ( H≅) = Unit
valueHeadType ( H𝟙) = Unit
valueHeadType ( H𝟘) = Unit
valueHeadType ( HType) = GHead
valueHeadType ( (HCtor tyCtor)) = DName tyCtor
valueHeadType HCumul = GHead

valueGHeadType : GHead → Set
valueGHeadType H⁇ = Σ[ h ∈ TyHead ] ValHead (HStatic h)
valueGHeadType H℧ = ⊥
valueGHeadType (HStatic h) = valueHeadType h


data ValHead where
  VH℧ : ∀ {h} → ValHead h
  VH⁇⁇ : ValHead H⁇
  VH⁇ : ∀ {h} → ValHead (HStatic h)
  HVal : ∀ {h} → valueHeadType h → ValHead (HStatic h)
  HVIn⁇ : (h : TyHead) → ValHead (HStatic h) → ValHead H⁇

HVIn⁇-inj : ∀ {h1 h2 : TyHead} → {x : ValHead (HStatic h1)} {y : ValHead (HStatic h2)} → HVIn⁇ h1 x ≡p HVIn⁇ h2 y → h1 ≡p h2
HVIn⁇-inj reflp = reflp



-- injHDataC : ∀ {c1 c2} (d1 : DName c1) (d2 : DName c2) → HData c1 d1 ≡p HData c2 d2 → c1 ≡p c2
-- injHDataC d1 d2 reflp = reflp

-- injHDataD : ∀ {c1 c2} (d1 : DName c1) (d2 : DName c2) → (pf : HData c1 d1 ≡p HData c2 d2) → pSubst (λ z → Fin (numCtors z)) (injHDataC d1 d2 pf  ) d1 ≡p d2
-- injHDataD d1 d2 reflp  = reflp


-- injHData : ∀ {c} (d1 : DName c) (d2 : DName c) → (pf : HData c d1 ≡p HData c d2) → d1 ≡p d2
-- injHData d1 d2 pf  = pTrans (pSym (helper d1 d2 pf)) (injHDataD d1 d2 pf)
--  where
--    helper :  ∀ {c} (d1 : DName c) (d2 : DName c) → (pf : HData c d1 ≡p HData c d2) → pSubst (λ z → Fin (numCtors z)) (injHDataC d1 d2 pf  ) d1 ≡p d1
--    helper d1 d2 pf  = pCong (λ eq → pSubst (λ z → Fin (numCtors z)) eq d1) (axKFin (injHDataC d1 d2 pf))

headDecEq : ∀ (h1 h2 : TyHead) → Dec (h1 ≡p h2)
headDecEq HΠ HΠ = yes reflp
headDecEq HΠ H≅ = no (λ ())
headDecEq HΠ HType = no (λ ())
headDecEq HΠ (HCtor x) = no (λ ())
headDecEq H≅ HΠ = no (λ ())
headDecEq H≅ H≅ = yes reflp
headDecEq H≅ HType = no (λ ())
headDecEq H≅ (HCtor x) = no (λ ())
headDecEq HType HΠ = no (λ ())
headDecEq HType H≅ = no (λ ())
headDecEq HType HType = yes reflp
headDecEq HType (HCtor x) = no (λ ())
headDecEq (HCtor x) HΠ = no (λ ())
headDecEq (HCtor x) H≅ = no (λ ())
headDecEq (HCtor x) HType = no (λ ())
headDecEq (HCtor x) (HCtor x₁) with decFin x x₁
... | yes reflp = yes reflp
... | no neq = no (λ {reflp → neq reflp})
-- headDecEq (HData c1 d1) (HData c2 d2 ) with decFin c1 c2
-- ... | no npf = no λ {reflp → npf reflp}
-- ... | yes reflp with decFin d1 d2 | isSetFin d1 d2
-- ... | no npf | x =  no λ {pf → npf (injHData d1 d2 pf)}
-- ... | yes reflp | _ = yes reflp
-- headDecEq HΠ (HData _ _) = no (λ ())
-- headDecEq H≅ (HData _ _) = no (λ ())
-- headDecEq HType (HData _ _) = no (λ ())
-- headDecEq (HCtor x) (HData _ x₁) = no (λ ())
-- headDecEq (HData _ x) HΠ = no (λ ())
-- headDecEq (HData _ x) H≅ = no (λ ())
-- headDecEq (HData _ x) HType = no (λ ())
-- headDecEq (HData _ x) (HCtor x₁) = no (λ ())
headDecEq HΠ HΣ = no (λ ())
headDecEq HΠ H𝟙 = no (λ ())
headDecEq HΠ H𝟘 = no (λ ())
headDecEq HΣ HΠ = no (λ ())
headDecEq HΣ HΣ = yes reflp
headDecEq HΣ H≅ = no (λ ())
headDecEq HΣ H𝟙 = no (λ ())
headDecEq HΣ H𝟘 = no (λ ())
headDecEq HΣ HType = no (λ ())
headDecEq HΣ (HCtor x) = no (λ ())
-- headDecEq HΣ (HData tyCtor x) = no (λ ())
headDecEq H≅ HΣ = no (λ ())
headDecEq H≅ H𝟙 = no (λ ())
headDecEq H≅ H𝟘 = no (λ ())
headDecEq H𝟙 HΠ = no (λ ())
headDecEq H𝟙 HΣ = no (λ ())
headDecEq H𝟙 H≅ = no (λ ())
headDecEq H𝟙 H𝟙 = yes reflp
headDecEq H𝟙 H𝟘 = no (λ ())
headDecEq H𝟙 HType = no (λ ())
headDecEq H𝟙 (HCtor x) = no (λ ())
-- headDecEq H𝟙 (HData tyCtor x) = no (λ ())
headDecEq H𝟘 HΠ = no (λ ())
headDecEq H𝟘 HΣ = no (λ ())
headDecEq H𝟘 H≅ = no (λ ())
headDecEq H𝟘 H𝟙 = no (λ ())
headDecEq H𝟘 H𝟘 = yes reflp
headDecEq H𝟘 HType = no (λ ())
headDecEq H𝟘 (HCtor x) = no (λ ())
-- headDecEq H𝟘 (HData tyCtor x) = no (λ ())
headDecEq HType HΣ = no (λ ())
headDecEq HType H𝟙 = no (λ ())
headDecEq HType H𝟘 = no (λ ())
headDecEq (HCtor x) HΣ = no (λ ())
headDecEq (HCtor x) H𝟙 = no (λ ())
headDecEq (HCtor x) H𝟘 = no (λ ())
headDecEq HΠ HCumul = no λ ()
headDecEq HΣ HCumul = no λ ()
headDecEq H≅ HCumul = no λ ()
headDecEq H𝟙 HCumul = no λ ()
headDecEq H𝟘 HCumul = no λ ()
headDecEq HType HCumul = no λ ()
headDecEq HCumul HΠ = no λ ()
headDecEq HCumul HΣ = no λ ()
headDecEq HCumul H≅ = no λ ()
headDecEq HCumul H𝟙 = no λ ()
headDecEq HCumul H𝟘 = no λ ()
headDecEq HCumul HType = no λ ()
headDecEq HCumul HCumul = yes reflp
headDecEq HCumul (HCtor x) = no λ ()
headDecEq (HCtor x) HCumul = no λ ()
-- headDecEq (HData tyCtor x) HΣ = no (λ ())
-- headDecEq (HData tyCtor x) H𝟙 = no (λ ())
-- headDecEq (HData tyCtor x) H𝟘 = no (λ ())

gheadDecEq : ∀ (x y : GHead) → Dec (x ≡p y)
gheadDecEq H⁇ H⁇ = yes reflp
gheadDecEq H⁇ H℧ = no λ ()
gheadDecEq H⁇ (HStatic x) = no λ ()
gheadDecEq H℧ H⁇ = no λ ()
gheadDecEq H℧ H℧ = yes reflp
gheadDecEq H℧ (HStatic x) = no λ ()
gheadDecEq (HStatic x) H⁇ = no λ ()
gheadDecEq (HStatic x) H℧ = no λ ()
gheadDecEq (HStatic x) (HStatic x₁) with headDecEq x x₁
... | yes reflp = yes reflp
... | no npf = no (λ {reflp → npf reflp})

injSigmaGenP : ∀  (x y : Σ TyHead (λ x → ValHead (HStatic x))) → (ppr : y ≡p x) → snd x ≡p pSubst (λ x → x) (pCong (λ x → ValHead (HStatic x)) (pCong fst ppr)) (snd y)
injSigmaGenP (x1 , x2) (y1 , y2) reflp = reflp


injSigmaP : (x : TyHead) → (y z : ValHead (HStatic x)) → _,_ {B = λ x → ValHead (HStatic x)} x y ≡p (x , z) → y ≡p z
injSigmaP x y z ppr with pgen ← injSigmaGenP (x , y) (x , z) (pSym ppr)
  rewrite Decidable⇒UIP.≡-irrelevant headDecEq (pCong fst (pSym ppr)) reflp = pgen

in⁇ToSigma : ∀ {ty1 ty2 : TyHead} → (x : ValHead (HStatic ty1)) → (y : ValHead (HStatic ty2)) → HVIn⁇ ty1 x ≡p HVIn⁇ ty2 y → _,_ {B = λ x → ValHead (HStatic x)} ty1 x ≡p (ty2 , y)
in⁇ToSigma x y reflp = reflp

valHeadDecEq : ∀ {h} (h1 h2 : ValHead h) → Dec (h1 ≡p h2)
valHeadTypeDecEq : ∀ {h} (h1 h2 : valueHeadType h) → Dec (h1 ≡p h2)

-- valHeadTypeDecEq {H⁇} (t1 , h1) (t2 , h2) with headDecEq t1 t2
-- ... | no npf = no (λ {reflp → npf reflp})
-- ... | yes reflp with valHeadDecEq h1 h2
-- ... | yes reflp = yes reflp
-- ... | no npf = no λ pf → npf (injSigmaP t1 h1 h2 pf)
valHeadTypeDecEq { HΠ} x y = yes reflp
valHeadTypeDecEq { HΣ} x y = yes reflp
valHeadTypeDecEq { H≅} x y = yes reflp
valHeadTypeDecEq { H𝟙} x y = yes reflp
valHeadTypeDecEq { H𝟘} x y = yes reflp
valHeadTypeDecEq { HType} x y = gheadDecEq x y
valHeadTypeDecEq { (HCtor x₁)} x y = decFin x y
valHeadTypeDecEq {HCumul} x y = gheadDecEq x y

valHeadDecEq {h} VH⁇ VH⁇ = yes reflp
valHeadDecEq {h} VH⁇ VH℧ = no λ ()
valHeadDecEq {h} VH⁇ (HVal x) = no λ ()
valHeadDecEq {h} VH℧ VH⁇ = no λ ()
valHeadDecEq {h} VH℧ VH℧ = yes reflp
valHeadDecEq {h} VH℧ (HVal x) = no λ ()
valHeadDecEq {h} (HVal x) VH⁇ = no λ ()
valHeadDecEq {h} (HVal x) VH℧ = no λ ()
valHeadDecEq {h} (HVal x) (HVal x₁) with valHeadTypeDecEq x x₁
... | yes reflp = yes reflp
... | no npf = no λ { reflp → npf reflp}
valHeadDecEq {H⁇} VH℧ (HVIn⁇ h y) = no λ ()
valHeadDecEq {H⁇} (HVIn⁇ h x) VH℧ = no λ ()
valHeadDecEq {H⁇} (HVIn⁇ h x) (HVIn⁇ h₁ y) with headDecEq h h₁
... | no npf = no (λ { reflp → npf reflp})
... | yes reflp with valHeadDecEq x y
... | no npf = no (λ {pf → npf (injSigmaP h x y (in⁇ToSigma x y pf))})
... | yes reflp = yes reflp
valHeadDecEq {.H⁇} VH℧ VH⁇⁇ = no λ ()
valHeadDecEq {.H⁇} VH⁇⁇ VH℧ = no λ ()
valHeadDecEq {.H⁇} VH⁇⁇ VH⁇⁇ = yes reflp
valHeadDecEq {.H⁇} VH⁇⁇ (HVIn⁇ h y) = no λ ()
valHeadDecEq {.H⁇} (HVIn⁇ h x) VH⁇⁇ = no λ ()

codeHead : ∀ {ℓ} → (c : ℂ ℓ) → GHead
codeHead C⁇ = H⁇
codeHead C℧ = H℧
codeHead C𝟘 = HStatic H𝟘
codeHead C𝟙 = HStatic H𝟙
codeHead CType = HStatic HType
codeHead (CΠ c cod) = HStatic HΠ
codeHead (CΣ c cod) = HStatic HΣ
codeHead (C≡ c x y) = HStatic H≅
codeHead (Cμ tyCtor c D x) = HStatic (HCtor tyCtor)
codeHead {ℓ = suc ℓ} (CCumul x) = HStatic HCumul
-- codeHead {suc ℓ} (CCumul t) = codeHead t

valueHead : ∀ {{_ : Æ}} {ℓ h} (c : ℂ ℓ) → (codeHead c ≡p h) → El c → ValHead h
valueHead C℧ _ x = VH℧
valueHead {ℓ = suc ℓ} (CCumul c) reflp x = HVal (HStatic HCumul)
valueHead C𝟘 _ tt = VH℧
valueHead C𝟙 _ false = VH℧
valueHead C𝟙 reflp true = HVal tt
valueHead {suc ℓ} CType reflp x = HVal (codeHead x)
valueHead (CΠ c cod) reflp x = HVal tt
valueHead (CΣ c cod) reflp x = HVal tt
valueHead (C≡ c x₁ y) reflp x = HVal tt
valueHead (CodeModule.Cμ tyCtor c D x₁) reflp (Wsup (FC (d , _) _ _)) = HVal d
valueHead (CodeModule.Cμ tyCtor c D x₁) reflp W℧ = VH℧
valueHead (CodeModule.Cμ tyCtor c D x₁) reflp W⁇ = VH⁇
valueHead C⁇ reflp ⁇⁇ = VH⁇⁇
valueHead C⁇ reflp ⁇℧ = VH℧
valueHead C⁇ reflp ⁇𝟙 = HVIn⁇ H𝟙 (HVal tt)
valueHead {suc ℓ} C⁇ reflp (⁇Type x) = HVIn⁇ HType (HVal (HStatic HType))
valueHead C⁇ reflp (⁇Π x) = HVIn⁇ HΠ (HVal tt)
valueHead C⁇ reflp (⁇Σ x) = HVIn⁇ HΣ (HVal tt)
valueHead C⁇ reflp (⁇≡ x) = HVIn⁇ H≅ (HVal tt)
valueHead C⁇ reflp (⁇μ tyCtor (Wsup (FC (d , _) _ _ ))) = HVIn⁇ (HCtor tyCtor) (HVal d)
valueHead C⁇ reflp (⁇μ tyCtor W℧) = VH℧
valueHead C⁇ reflp (⁇μ tyCtor W⁇) = HVIn⁇ (HCtor tyCtor) VH⁇
valueHead  CodeModule.C⁇ reflp (CodeModule.⁇Cumul x) = HVIn⁇ HCumul (HVal {!!})


data HeadMatchView : GHead → GHead → Set where
  H℧L : ∀ {h1 h2 } → h1 ≡p H℧ → HeadMatchView h1 h2
  H℧R : ∀ {h1 h2 } → h2 ≡p H℧ → HeadMatchView h1 h2
  H⁇L : ∀ {h1 h2} → h1 ≡p H⁇ → ¬ (h2 ≡p H℧) → HeadMatchView h1 h2
  H⁇R : ∀ {h1 h2} → h2 ≡p H⁇ → HeadMatchView (HStatic h1) h2
  HEq : ∀ {h1 h2} → h1 ≡p h2 → HeadMatchView (HStatic h1) (HStatic h2)
  HNeq : ∀ {h1 h2} → ¬ (h1 ≡p h2) → HeadMatchView (HStatic h1) (HStatic h2)

headMatchView : ∀ h1 h2 → HeadMatchView h1 h2
headMatchView H℧ h2 = H℧L reflp
headMatchView H⁇ H⁇ = H⁇L reflp λ ()
headMatchView H⁇ H℧ = H℧R reflp
headMatchView H⁇ (HStatic x) = H⁇L reflp (λ ())
headMatchView (HStatic x) H⁇ = H⁇R reflp
headMatchView (HStatic x) H℧ = H℧R reflp
headMatchView (HStatic h1) (HStatic h2) with headDecEq h1 h2
... | yes pf = HEq pf
... | no npf = HNeq npf

-- reverseHMV : ∀ {h1 h2} →  HeadMatchView h1 h2 → HeadMatchView h2 h1
-- reverseHMV (H℧L x) = H℧R x
-- reverseHMV (H℧R x) = H℧L x
-- reverseHMV {H⁇} {h2 = H⁇} (H⁇L x x₁) = H⁇L reflp (λ ())
-- reverseHMV {H⁇} {h2 = H℧} (H⁇L x x₁) with () ← x₁ reflp
-- reverseHMV {H⁇} {h2 = HStatic x₂} (H⁇L x x₁) = H⁇R x
-- reverseHMV (H⁇R x) = H⁇L x (λ ())
-- reverseHMV (HEq x) = HEq (pSym x)
-- reverseHMV (HNeq x) = HNeq (λ pf → x (pSym pf) )



data ValHeadMatchView  : {h : GHead} →  ValHead h → ValHead h → Set where
  VH℧L : ∀ {h} {h1 h2 : ValHead h} → h1 ≡p VH℧ → ValHeadMatchView h1 h2
  VH℧R : ∀ {h} {h1 h2 : ValHead h} → h2 ≡p VH℧ → ValHeadMatchView h1 h2
  VH⁇L : ∀ {h} {h1 h2 : ValHead (HStatic h)} → h1 ≡p VH⁇ → ¬ (h2 ≡p VH℧) → ValHeadMatchView h1 h2
  VH⁇R : ∀ {h} {x : valueHeadType h} {h2 : ValHead (HStatic h)} → h2 ≡p VH⁇ → ValHeadMatchView (HVal x) h2
  VHEq : ∀ {h} {x y : valueHeadType h} → x ≡p y → ValHeadMatchView (HVal x) (HVal y)
  VHNeq : ∀ {h} {x y : valueHeadType h} → ¬ (x ≡p y) → ValHeadMatchView (HVal x) (HVal y)
  VHIn⁇L : ∀  {h1 h2 : ValHead H⁇} → h1 ≡p VH⁇⁇ → ¬ (h2 ≡p VH℧) → ValHeadMatchView h1 h2
  VHIn⁇R : ∀ {h } {h1 : ValHead (HStatic h)} {h2 : ValHead H⁇} → h2 ≡p VH⁇⁇ → ValHeadMatchView (HVIn⁇ h h1) h2
  VHEq⁇ : ∀ {h} {h1 h2 : ValHead (HStatic h)} → h1 ≡p h2 → ValHeadMatchView (HVIn⁇ h h1) (HVIn⁇ h h2)
  VHNeq⁇ : ∀ {ty1 ty2} {h1 : ValHead (HStatic ty1)} {h2 : ValHead (HStatic ty2)} → ¬ ((HVIn⁇ ty1 h1) ≡p (HVIn⁇ ty2 h2 )) → ValHeadMatchView (HVIn⁇ ty1 h1) (HVIn⁇ ty2 h2)



valHeadMatchView : ∀ {h} (h1 h2 : ValHead h) → ValHeadMatchView h1 h2
valHeadMatchView VH℧ h2 = VH℧L reflp
valHeadMatchView h1 VH℧ = VH℧R reflp
valHeadMatchView VH⁇⁇ VH⁇⁇ = VHIn⁇L reflp (λ ())
valHeadMatchView (HVIn⁇ h h1) VH⁇⁇ = VHIn⁇R reflp
valHeadMatchView VH⁇ VH⁇ = VH⁇L reflp (λ ())
valHeadMatchView (HVal x) VH⁇ = VH⁇R reflp
valHeadMatchView VH⁇ (HVal x) = VH⁇L reflp (λ ())
valHeadMatchView (HVal x) (HVal y) with valHeadTypeDecEq x y
... | yes pf = VHEq pf
... | no npf = VHNeq npf
valHeadMatchView VH⁇⁇ (HVIn⁇ h h2) = VHIn⁇L reflp (λ ())
valHeadMatchView (HVIn⁇ ty1 h1) (HVIn⁇ ty2 h2) with valHeadDecEq (HVIn⁇ ty1 h1) (HVIn⁇ ty2 h2)
... | yes reflp = VHEq⁇ reflp
... | no npf = VHNeq⁇ npf
