{-# OPTIONS --rewriting #-}
open import Cubical.Data.Nat
open import Source.SyntaxParams
open import Cubical.Data.FinData
open import Cubical.Data.Bool
import Cubical.Data.Vec as V
open import Cubical.Data.Vec using (Vec)
open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod hiding (map)
open import DecPEq
open import Cubical.Data.Equality

module Source.Syntax  {{_ : Language}} {{_ : Inductives}} where

--Syntax for our source language
--We express it using Abstract Binding Trees to take care of substitution
--

open import Cubical.Data.List
import Cubical.Data.Vec as V
open import Cubical.Data.Vec using (Vec)

repeat : ∀ {ℓ} {A : Set ℓ} → ℕ → A → List A
repeat zero x = []
repeat (suc n) x = x ∷ repeat n x

concat : ∀ {ℓ} {A : Set ℓ} → List (List A) → List A
concat [] = []
concat (l ∷ l₁) = l ++ concat l₁

toList : ∀ {ℓ} {A : Set ℓ} {n} → Vec A n → List A
toList V.[] = []
toList (x V.∷ xs) = x ∷ toList xs

toListLen : ∀ {ℓ} {A : Set ℓ} {n} → (v : Vec A n) → length (toList v) ≡p n
toListLen V.[] = reflp
toListLen (x V.∷ v) = pCong suc (toListLen v)

open import Syntax




data OpI : SyntaxType → Set where
    -- Types
    OType : ℕ →  OpI Ty
    --Functions
    OΠ : OpI Ty
    Oλ : OpI Lam
    OApp : OpI Elim
    --Inductives
    OC : CName → ℕ → OpI Ty
    OD : (c : CName) → DName c → ℕ → OpI Intro
    OInd : CName → ℕ → OpI Elim
    --Equality
    O≡ : OpI Ty
    ORefl : OpI Intro
    OJ : OpI Elim
    -- Gradual terms and casts
    OUnk : {{_ : InLang Surface}} → ℕ → OpI SurfUnk
    O⁇ : {{_ : InLang Cast }} → OpI ⁇℧Syn
    OCast : {{_ : InLang Cast }} →  OpI CastSyn
    O℧ : {{_ : InLang Cast }} → OpI ⁇℧Syn
    OTag : {{_ : InLang Cast }} → ℕ → OpI Ty →  OpI CastSyn
    OMeet : {{_ : InLang Cast }} →  OpI CastSyn

data AST : Set where
  -- x∙_ : AST → AST
  Svar : ℕ → AST
  SUnk : ∀ {{_ : InLang Surface}} → ℕ → AST
  S⁇ : {{_ : InLang Cast }} → AST → AST
  STag : {{_ : InLang Cast }} → ℕ → OpI Ty → AST → AST
  S℧ : {{_ : InLang Cast}} → AST → AST
  SCast : {{_ : InLang Cast}} → AST → AST → AST → AST
  SΠ : AST → AST → AST
  Sλ : AST → AST → AST
  SApp : AST → AST → AST
  SType : ℕ → AST
  SC : (c : CName) →  ℕ → Vec AST (arityC c + numIxC c) → AST
  SD : (c : CName) → (d : DName c) → ℕ → Vec AST (arityC c + numIxC c + arityD c d) → AST
  Sind : (c : CName) → ℕ → AST → AST → Vec AST (numCtors c) → AST
  S≡ : AST → AST → AST → AST
  SRefl : AST → AST → AST → AST
  SJ : AST → AST → AST → AST → AST → AST
  SMeet : {{_ : InLang Cast}} → AST → AST → AST → AST


    -- ? in the surface language, only labeled with level

-- Op is the sum of all allowed language types
record Op : Set where
  constructor op
  field
    {lty} : SyntaxType
    theOp : OpI lty


-- elimBind : CName → List Sig
-- elimBind c = (map (λ d → nBinds (1 + numIxC c + arityD c d)) (allCtors c))

nBinds : ℕ → Sig
nBinds zero = ■
nBinds (suc n) = ν (nBinds n)

sig : Op → List Sig
sig (op (OType i)) = []
sig (op OΠ) = ■ ∷ ν ■ ∷ []
sig (op Oλ) = ■ ∷ ν ■ ∷ []
sig (op OApp) = ■ ∷ ■ ∷ []
sig (op (OC c _)) = repeat (arityC c + numIxC c) ■
sig (op (OD c d _)) = repeat ((arityC c + numIxC c) + arityD c d) ■
sig (op (OInd c _)) = ■ ∷ ν ■ ∷ toList (V.map (λ d → nBinds (1 + (numIxC c + arityD c d))) (allCtors c))
sig (op OCast) = ■ ∷ ■ ∷ ■ ∷ []
sig (op O⁇) = [ ■ ]
sig (op (OUnk i)) = []
sig (op O℧) = [ ■ ]
sig (op O≡) = ■ ∷ ■ ∷ ■ ∷ []
sig (op ORefl) = ■ ∷ ■ ∷ ■ ∷ []
sig (op OJ) = ν ■ ∷ ■ ∷ ■ ∷ ■ ∷ ■ ∷ []
sig (op (OTag i _)) = [ ■ ]
sig (op (OMeet)) = ■ ∷ ■ ∷ ■ ∷ []



----------
--Go between our sytnax reprs

open import Sig public
open import Var public
open import Substitution public
-- open Syntax.OpSig Op sig public hiding (_[_])
open import AbstractBindingTree Op sig public
open Substitution.ABTOps Op sig public
open import WellScoped Op sig public


splitArgs : ∀ {l1 l2} → Args (l1 ++ l2) → Args l1 × Args l2
splitArgs {l1 = []} args = nil , args
splitArgs {l1 = x ∷ l1} {l2} (cons arg args) with (retL , retR) ← splitArgs {l1} {l2 = l2} args
  = cons arg retL , retR

-- Our syntax definition is equivalent to the ABT version
--
ABT→AST : ABT → AST
fromArg : ∀ {sig} → Arg sig → AST
fromRepeat : ∀ {n} → Args (repeat n ■) → Vec AST n
argsToVec : ∀ {l : List Sig} {n} → Args l → length l ≡p n → Vec AST n

splitRepeat : ∀ {ℓ} {A : Set ℓ} m { n} {x : A} → repeat (m + n) x ≡ repeat m x ++ repeat n x
splitRepeat zero = refl
splitRepeat (suc m) {x = x} = cong (x ∷_) (splitRepeat m)

fromArg (ast x) = ABT→AST x
fromArg (bind a) = fromArg a
fromArg (clear a) = fromArg a

ABT→AST (` x) = Svar x
ABT→AST (op (OType i) ⦅ nil ⦆) = SType i
ABT→AST (op OΠ ⦅ cons (ast Dom) (cons (bind (ast Cod)) nil) ⦆) = SΠ (ABT→AST Dom) (ABT→AST Cod)
ABT→AST (op Oλ ⦅ cons (ast Dom) (cons (bind (ast x)) nil) ⦆) = Sλ (ABT→AST Dom) (ABT→AST x)
ABT→AST (op OApp ⦅  (cons (ast x) (cons (ast y) nil)) ⦆) = SApp (ABT→AST x) (ABT→AST y)
ABT→AST (op (OC c i) ⦅ x ⦆) = SC c i (fromRepeat x)
ABT→AST (op (OD c d i) ⦅ x ⦆) = SD c d i (fromRepeat x)
ABT→AST (op (OInd c i) ⦅ cons (ast disc) (cons (bind (ast T)) cases) ⦆) = Sind c i (ABT→AST disc) (ABT→AST T) (argsToVec cases (toListLen (V.map (λ d → ν (nBinds (numIxC c + arityD c d ))) (allCtors c))))
ABT→AST (op O≡ ⦅ cons (ast T) (cons (ast x) (cons (ast y) nil)) ⦆) = S≡ (ABT→AST T) (ABT→AST x) (ABT→AST y)
ABT→AST (op ORefl ⦅ cons (ast wit) (cons (ast x) (cons (ast y) nil)) ⦆) = SRefl (ABT→AST wit) (ABT→AST x) (ABT→AST y)
ABT→AST (op OJ ⦅ cons (bind (ast T)) (cons (ast P) (cons (ast x) (cons (ast y) (cons (ast pf) nil))) ) ⦆) = SJ (ABT→AST T) (ABT→AST P) (ABT→AST x) (ABT→AST y) (ABT→AST pf)
ABT→AST (op O⁇ ⦅ cons (ast T) nil ⦆) = S⁇ (ABT→AST T)
ABT→AST (op O℧ ⦅ cons (ast T) nil ⦆) = S℧ (ABT→AST T)
ABT→AST (op OCast ⦅ cons (ast To) (cons (ast From) (cons (ast x) nil)) ⦆) = SCast (ABT→AST To) (ABT→AST From) (ABT→AST x)
ABT→AST (op (OUnk i) ⦅ x ⦆) = SUnk i
ABT→AST (op (OTag i h ) ⦅ cons (ast t) nil ⦆) = STag i h (ABT→AST t)
ABT→AST (op (OMeet ) ⦅ cons (ast T) (cons (ast t) (cons (ast t₂) nil)) ⦆) = SMeet (ABT→AST T) (ABT→AST t) (ABT→AST t₂)

fromRepeat {zero} nil = V.[]
fromRepeat {suc n} (cons (ast x) rest) = (ABT→AST x) V.∷ fromRepeat { n = n } rest

suc-inj : ∀ {m n} → suc m ≡p suc n → m ≡p n
suc-inj reflp = reflp

argsToVec nil reflp = V.[]
argsToVec {n = zero} (cons a rest) ()
argsToVec {n = suc n} (cons a rest) pf = (fromArg a) V.∷ (argsToVec rest (suc-inj  pf))

AST→ABT : AST → ABT
toRepeat : ∀ {n} → Vec AST n → Args (repeat n ■)
toArg : ∀ {sig} → AST → Arg sig
argsFromVec : ∀ {n} (sigs : Vec Sig n) → Vec AST n →  Args (toList sigs)


AST→ABT (Svar x) = ` x
AST→ABT (SUnk i) = (op (OUnk i)) ⦅ nil ⦆
AST→ABT (S⁇ x) = (op O⁇) ⦅ cons (ast (AST→ABT x)) nil ⦆
AST→ABT (STag i h t) = (op (OTag i h)) ⦅ cons (ast (AST→ABT t)) nil ⦆
AST→ABT (SMeet T t₁ t₂) = (op (OMeet)) ⦅ cons (ast (AST→ABT T)) (cons (ast (AST→ABT t₁)) (cons (ast (AST→ABT t₂)) nil)) ⦆
AST→ABT (S℧ x) = (op O℧) ⦅ cons (ast (AST→ABT x)) nil ⦆
AST→ABT (SCast x x₁ x₂) = (op OCast) ⦅ cons (ast (AST→ABT x)) (cons (ast (AST→ABT x₁)) (cons (ast (AST→ABT x₂)) nil)) ⦆
AST→ABT (SΠ x x₁) = (op OΠ) ⦅ cons (ast (AST→ABT x)) (cons (bind (ast (AST→ABT x₁))) nil) ⦆
AST→ABT (Sλ T t) = (op Oλ) ⦅ cons (ast (AST→ABT T)) (cons (bind (ast (AST→ABT t))) nil) ⦆
AST→ABT (SApp x x₁) = (op OApp) ⦅ cons (ast (AST→ABT x)) (cons (ast (AST→ABT x₁)) nil) ⦆
AST→ABT (SType i) = (op (OType i)) ⦅ nil ⦆
AST→ABT (SC c i x₁) = (op (OC c i)) ⦅ toRepeat x₁ ⦆
AST→ABT (SD c d i x₁) = (op (OD c d i)) ⦅ toRepeat x₁ ⦆
AST→ABT (Sind c i x₁ x₂ x₃) = (op (OInd c i)) ⦅ cons (ast (AST→ABT x₁)) (cons (bind (ast (AST→ABT x₂))) (argsFromVec (V.map (λ d → nBinds (1 + (numIxC c + arityD c d))) (allCtors c)) x₃)) ⦆
AST→ABT (S≡ x x₁ x₂) = (op O≡) ⦅ cons (ast (AST→ABT x)) (cons (ast (AST→ABT x₁)) (cons (ast (AST→ABT x₂)) nil)) ⦆
AST→ABT (SRefl x x₁ x₂) = (op ORefl) ⦅ cons (ast (AST→ABT x)) (cons (ast (AST→ABT x₁)) (cons (ast (AST→ABT x₂)) nil)) ⦆
AST→ABT (SJ x x₁ x₂ x₃ x₄) =
  (op OJ) ⦅ cons (bind (ast (AST→ABT x))) (cons (ast (AST→ABT x₁)) (cons (ast (AST→ABT x₂)) (cons (ast (AST→ABT x₃)) (cons (ast (AST→ABT x₄)) nil)))) ⦆

toRepeat {zero} x = nil
toRepeat {suc n} (x V.∷ x₁) = cons (ast (AST→ABT x) ) (toRepeat x₁)

toArg {sig = ■} x = ast (AST→ABT x)
toArg {sig = ν sig₁} x = bind (toArg x)
toArg {sig = ∁ sig₁} x = clear (toArg x)

argsFromVec V.[] V.[] = nil
argsFromVec (x V.∷ sigs) (x₁ V.∷ ts) = cons (toArg x₁) (argsFromVec sigs ts)



syntaxToFrom : ∀ x → AST→ABT (ABT→AST x) ≡p x
syntaxFromTo : ∀ x → ABT→AST (AST→ABT x) ≡p x
argToFrom : ∀ {sig} x → toArg {sig = sig} (fromArg {sig = sig} x) ≡p x
argFromTo : ∀ {sig} x → fromArg {sig = sig} (toArg {sig = sig} x) ≡p x
repeatFromTo : ∀ {n} x → fromRepeat {n} (toRepeat x) ≡p x
repeatToFrom : ∀ {n} x → toRepeat {n} (fromRepeat x) ≡p x
argsVecToFrom : ∀ {n} {sigs : Vec Sig n} (ts : Vec AST n) → argsToVec (argsFromVec sigs ts) (toListLen sigs) ≡p ts
argsVecFromTo : ∀ {n} {sigs : Vec Sig n} (args : Args (toList sigs)) → argsFromVec sigs (argsToVec args (toListLen sigs)) ≡p args


syntaxToFrom (` x) = reflp
syntaxToFrom (op (OType i) ⦅ nil ⦆) = reflp
syntaxToFrom (op OΠ ⦅ cons (ast Dom) (cons (bind (ast Cod)) nil) ⦆)
  rewrite syntaxToFrom Dom | syntaxToFrom Cod = reflp
syntaxToFrom (op Oλ ⦅ cons (ast Dom) (cons (bind (ast x)) nil) ⦆)
  rewrite syntaxToFrom Dom | syntaxToFrom x = reflp
syntaxToFrom (op OApp ⦅  (cons (ast x) (cons (ast y) nil)) ⦆)
  rewrite syntaxToFrom x | syntaxToFrom y = reflp
syntaxToFrom (op (OC c i) ⦅ x ⦆) rewrite repeatToFrom x = reflp
syntaxToFrom (op (OD c d i) ⦅ x ⦆) rewrite repeatToFrom x = reflp
syntaxToFrom (op (OInd c i) ⦅ cons (ast disc) (cons (bind (ast T)) cases) ⦆)
  rewrite syntaxToFrom disc | syntaxToFrom T | argsVecFromTo cases = reflp
syntaxToFrom (op O≡ ⦅ cons (ast T) (cons (ast x) (cons (ast y) nil)) ⦆)
  rewrite syntaxToFrom T | syntaxToFrom x | syntaxToFrom y = reflp
syntaxToFrom (op ORefl ⦅ cons (ast wit) (cons (ast x) (cons (ast y) nil)) ⦆)
  rewrite syntaxToFrom wit | syntaxToFrom x | syntaxToFrom y = reflp
syntaxToFrom (op OJ ⦅ cons (bind (ast T)) (cons (ast P) (cons (ast x) (cons (ast y) (cons (ast pf) nil))) ) ⦆)
  rewrite syntaxToFrom T | syntaxToFrom P | syntaxToFrom x | syntaxToFrom y | syntaxToFrom pf = reflp
syntaxToFrom (op O⁇ ⦅ cons (ast T) nil ⦆)
  rewrite syntaxToFrom T = reflp
syntaxToFrom (op O℧ ⦅ cons (ast T) nil ⦆)
  rewrite syntaxToFrom T = reflp
syntaxToFrom (op OCast ⦅ cons (ast To) (cons (ast From) (cons (ast x) nil)) ⦆)
  rewrite syntaxToFrom To | syntaxToFrom From | syntaxToFrom x = reflp
syntaxToFrom (op (OUnk i) ⦅ nil ⦆) = reflp
syntaxToFrom (op (OTag i h) ⦅ cons (ast t) nil ⦆)
  rewrite syntaxToFrom t = reflp
syntaxToFrom (op (OMeet) ⦅ cons (ast T) (cons (ast t) (cons (ast t₂) nil)) ⦆)
  rewrite syntaxToFrom t | syntaxToFrom t₂ | syntaxToFrom T = reflp

repeatToFrom {zero} nil = reflp
repeatToFrom {suc n} (cons (ast x) rest) rewrite repeatToFrom rest | syntaxToFrom x = reflp

syntaxFromTo (Svar x) = reflp
syntaxFromTo (SUnk x) = reflp
syntaxFromTo (STag i h t)
  rewrite syntaxFromTo t = reflp
syntaxFromTo (SMeet T t t₂)
  rewrite syntaxFromTo t | syntaxFromTo t₂ | syntaxFromTo T = reflp
syntaxFromTo (S⁇ t) rewrite syntaxFromTo t = reflp
syntaxFromTo (S℧ t) rewrite syntaxFromTo t = reflp
syntaxFromTo (SCast t t₁ t₂)
  rewrite syntaxFromTo t | syntaxFromTo t₁ | syntaxFromTo t₂ = reflp
syntaxFromTo (SΠ t t₁)
  rewrite syntaxFromTo t | syntaxFromTo t₁ = reflp
syntaxFromTo (Sλ t t₁)
  rewrite syntaxFromTo t | syntaxFromTo t₁ = reflp
syntaxFromTo (SApp t t₁)
  rewrite syntaxFromTo t | syntaxFromTo t₁ = reflp
syntaxFromTo (SType i) = reflp
syntaxFromTo (SC c x x₁) rewrite repeatFromTo x₁ = reflp
syntaxFromTo (SD c d x x₁) rewrite repeatFromTo x₁ = reflp
syntaxFromTo (Sind c x t t₁ rhses)
  rewrite syntaxFromTo t | syntaxFromTo t₁ | argsVecToFrom {sigs = V.map (λ d → nBinds (1 + (numIxC c + arityD c d))) (allCtors c)} rhses = reflp
syntaxFromTo (S≡ t t₁ t₂)
  rewrite syntaxFromTo t | syntaxFromTo t₁ | syntaxFromTo t₂ = reflp
syntaxFromTo (SRefl t t₁ t₂)
  rewrite syntaxFromTo t | syntaxFromTo t₁ | syntaxFromTo t₂ = reflp
syntaxFromTo (SJ t t₁ t₂ t₃ t₄)
  rewrite syntaxFromTo t | syntaxFromTo t₁ | syntaxFromTo t₂ | syntaxFromTo t₃ | syntaxFromTo t₄ = reflp

repeatFromTo {zero} V.[] = reflp
repeatFromTo {suc n} (x V.∷ x₁) rewrite syntaxFromTo x | repeatFromTo x₁ = reflp

argsVecFromTo {sigs = sigs} args with toListLen sigs
argsVecFromTo {sigs = V.[]} nil | reflp = reflp
argsVecFromTo {sigs = x V.∷ sigs} (cons arg args) | pf rewrite argToFrom arg | uipNat (suc-inj pf) (toListLen sigs)   = pCong (cons arg) (argsVecFromTo args)

argsVecToFrom {sigs = sigs} ts with toListLen sigs
argsVecToFrom {sigs = V.[]} V.[] | reflp = reflp
argsVecToFrom {sigs = sig V.∷ sigs} (x V.∷ rest) | pf rewrite argFromTo {sig = sig} x rewrite uipNat (suc-inj pf) (toListLen sigs) = (pCong (λ x → _ V.∷ x) (argsVecToFrom rest))

argToFrom (ast x) = pCong ast (syntaxToFrom x)
argToFrom (bind x) = pCong bind (argToFrom x)
argToFrom (clear x) = pCong clear (argToFrom x)

argFromTo {■} x = syntaxFromTo x
argFromTo {ν sig₁} x = argFromTo {sig₁} x
argFromTo {∁ sig₁} x = argFromTo {sig₁} x

-- open import Agda.Builtin.Equality
-- open import Agda.Builtin.Equality.Rewrite


-- Notation for ASTs
pattern λx⦂_∙_ T t = Sλ T t
pattern _$_ x y = SApp x y

pattern ⟨_⇐_⟩_ To From x = SCast To From x
pattern ⟨_⇐_⟩_ To From x = SCast To From x

pattern _≡[_]_ x T y = S≡ T x y

pattern _⊢_≅_ e x y = SRefl e x y

pattern [x⦂_]⟶_ S T = SΠ S T

pattern ⁇[_] T = S⁇ T
pattern ℧[_] T = S℧ T

pattern _&[_]_ s T t = SMeet T s t

refl[_] : AST → AST
refl[ x ] = SRefl x x x



infixr 100 _^_[_,,_]

_^_[_,,_] : (c : CName) → ℕ → Vec AST (arityC c) → Vec AST (numIxC c) → AST
C ^ i [ pars ,, ixs ] = SC C i (pars V.++ ixs)

infixr 100 _^_[_,,_,,_]

_^_[_,,_,,_] : ∀{c : CName} (d : DName c) → ℕ → Vec AST (arityC c) → Vec AST (numIxC c) → Vec AST (arityD c d) → AST
d ^ i [ pars ,, ixs ,, args ] = SD _ d i ((pars V.++ ixs) V.++ args)

⁇or℧[_][_] : OpI ⁇℧Syn → AST → AST
⁇or℧[ O⁇ ][ T ] = ⁇[ T ]
⁇or℧[ O℧ ][ T ] = ℧[ T ]



{-# REWRITE syntaxFromTo syntaxToFrom #-}
