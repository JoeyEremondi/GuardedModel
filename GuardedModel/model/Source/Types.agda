

open import Source.SyntaxParams
open import Source.Tele {{CastCalc}}

module Source.Types  {{ _ : Inductives }} {{_ : IndParams }}  where

open import DecPEq
open import Cubical.Data.Equality
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.FinData
open import Source.Syntax {{CastCalc }}
open import Source.Sub
open import Source.Germ
open import Source.Redex

data Mode : Set where
  Synth : Mode
  Check : Mode
  PSynth : (OpI Ty) → Mode

private variable
  ⇐⇒ : Mode
  n  x i j : ℕ
  Γ : Vec AST n
  t t₀ t₁ t₂ t₃ T T₀ T₁ T₂ T₃ ε pf scrut Tₚ : AST
  h :  (OpI Ty)

data _⊢_[_]_ :  ∀ {n} → (Γ : Vec AST n) → AST → Mode → AST → Prop
_⊢_⇒_ : ∀ {n} → (Γ : Vec AST n) → AST →  AST → Prop
_⊢_⇐_ : ∀ {n} → (Γ : Vec AST n) → AST →  AST → Prop
_⊢_⇒[_]_ : ∀ {n} → (Γ : Vec AST n) → AST → OpI Ty → AST → Prop

Γ ⊢ t ⇒ T  = Γ ⊢ t [ Synth ] T
Γ ⊢ t ⇐ T  = Γ ⊢ t [ Check ] T
Γ ⊢ t ⇒[ h ]  T = Γ ⊢ t [ PSynth h ] T

data _[_]≔_ {n} : Vec AST n → ℕ → AST → Set  where
  envLook :  (f : Fin n) → toℕ f ≡p n → Γ [ x ]≔ (lookup f Γ )

data _⊢_[_]_ where


    Var⇒ :
       Γ [ x ]≔ T  →
      ----------------------------------
      Γ ⊢ Svar x ⇒ T


    Ty⇒  :
      ----------------------------------
      Γ ⊢ SType i ⇒ SType (suc i)


    Pi⇒ :
      Γ ⊢ T₁ ⇒[ OType 0 ] SType i →
      (T₁ ∷ Γ) ⊢ T₂ ⇒[ OType 0 ] SType j →
      ----------------------------------
      Γ ⊢ [x⦂ T₁ ]⟶ T₂ ⇒ SType (max i j)


    Lam⇒  :
      (T₁ ∷ Γ) ⊢ t ⇒ T₂  →
      -----------------------------------------
      Γ ⊢ λx⦂ T ∙ t ⇒ ([x⦂ T₁ ]⟶ T₂)


    App⇒  :
      Γ ⊢ t₀ ⇒[ OΠ  ] ([x⦂ T₁ ]⟶ T₂)  →
      Γ ⊢ t₁ ⇐ T₁  →
      -------------------------------------
      Γ ⊢ t₀ $ t₁ ⇒ ([ t₁ /x] T₂)


    Eq⇒  :
      Γ ⊢ T ⇒[ OType 0 ] (SType i) →
      Γ ⊢ t₁ ⇐ T →
      Γ ⊢ t₂ ⇐ T →
      --------------------------------------
      Γ ⊢ (t₁ ≡[ T ] t₂ ) ⇒ SType i


    Refl⇒ :
        Γ ⊢ ε ⇒ T →
        Γ ⊢ t₁ ⇐ T →
        Γ ⊢ t₂ ⇐ T →
        -------------------------------------
        Γ ⊢ (ε ⊢ t₁ ≅ t₂) ⇒ (t₁ ≡[ T  ] t₂ )


    J⇒ :
      Γ ⊢ pf ⇒[ O≡ ] (t₁ ≡[ T  ] t₂) →
      (T ∷ Γ) ⊢ Tₚ ⇒[ OType 0 ] (SType i) →
      Γ ⊢ t ⇐ ([ t₁ /x] Tₚ) →
      --------------------------------------
      Γ ⊢ (SJ Tₚ t₁ t₂ t pf ) ⇒ ([ t₂ /x] Tₚ)


    Unk⇒  :
      Γ ⊢ T ⇒[ OType 0 ] SType i →
      ------------------------------------
      Γ ⊢ ⁇[ T ] ⇒ T

    Err⇒ :
      Γ ⊢ T ⇒[ OType 0 ] SType i →
      ------------------------------------
      Γ ⊢ ℧[ T ] ⇒ T

    Cast :
      Γ ⊢ T₁ ⇒[ OType 0 ] SType i →
      Γ ⊢ T₂ ⇒[ OType 0 ] SType i →
      Γ ⊢ t ⇐ T₁ →
      ----------------------------------
      Γ ⊢ ⟨ T₂ ⇐ T₁ ⟩ t ⇒ T₂

    Tag :
       Γ ⊢ t ⇐ Germ h i   →
      ----------------------------------
      Γ ⊢ STag i h t ⇒ ⁇[ SType i ]


    Check⇐ :
      Γ ⊢ t ⇒ T₂ →
       T₁ ≡↝ T₂  →
      ----------------------------------
      Γ ⊢ t ⇐ T₁

    PSynthΠ :
      Γ ⊢ t ⇒ T →
       T ≡↝ ([x⦂ T₁ ]⟶ T₂ ) →
      ---------------------------------------
      Γ ⊢ t ⇒[ OΠ ] ([x⦂ T₁ ]⟶ T₂ )

    PSynth≡ :
      Γ ⊢ t ⇒ T →
      T ≡↝ (t₁ ≡[ T ] t₂ ) →
      ---------------------------------------
      Γ ⊢ t ⇒[ O≡ ] (t₁ ≡[ T ] t₂)


    PSynthType : ∀ {j} →
      Γ ⊢ t ⇒ T →
      T ≡↝ (SType i) →
      ---------------------------------------
      Γ ⊢ t ⇒[ OType j ] (SType i)

