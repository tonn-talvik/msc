{-# OPTIONS --type-in-type #-}
module MyLanguage where

open import Relation.Nullary
open import Relation.Binary.Core using (_≡_ ; refl)

open import Function hiding (_$_)

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Product

open import Data.Nat hiding (_≟_)
open import Data.Bool hiding (T ; _≟_)
open import Data.Fin hiding (lift; _<_)
open import Data.List


open import Finiteness
  renaming (here to fhere)
--open import GradedMonad
--open import OrderedMonoid
--open import NonDeterminism

  
T : Set → Set
T X = List X

η : {X : Set} → X → T X
η x = [ x ]

lift : {X Y : Set} → (X → T Y) → T X → T Y
lift f []  = []
lift f (x ∷ xs) = f x ++ lift f xs

sfail : {X : Set} → T X
sfail = []

sor : {X : Set} → T X → T X → T X 
sor = _++_

----------------------------------------------------------------------
infixr 30 _⇒_
data VType : Set where
  nat : VType
  bool : VType
  _⇒_ : VType → VType → VType
  _∏_ : VType → VType → VType
  
⟦_⟧v : VType → Set
⟦ nat ⟧v = ℕ
⟦ bool ⟧v = Bool
⟦ t ⇒ u ⟧v = ⟦ t ⟧v → T ⟦ u ⟧v
⟦ t ∏ u ⟧v = ⟦ t ⟧v × ⟦ u ⟧v

----------------------------------------------------------------------

Ctx = List VType

⟦_⟧l : Ctx → Set
⟦ [] ⟧l = ⊤
⟦ σ ∷ Γ ⟧l = ⟦ σ ⟧v × ⟦ Γ ⟧l

----------------------------------------------------------------------

infixl 80 _$_

mutual
  data VTerm (Γ : Ctx) : VType → Set where
    TT FF : VTerm Γ bool
    ZZ : VTerm Γ nat
    SS : VTerm Γ nat → VTerm Γ nat
    ⟨_,_⟩ : ∀ {σ τ} → VTerm Γ σ → VTerm Γ τ → VTerm Γ (σ ∏ τ)
    FST : ∀ {σ τ} → VTerm Γ (σ ∏ τ) → VTerm Γ σ
    SND : ∀ {σ τ} → VTerm Γ (σ ∏ τ) → VTerm Γ τ
    VAR : ∀ {τ} → τ ∈ Γ → VTerm Γ τ
    LAM : ∀ σ {τ} → CTerm (σ ∷ Γ) τ → VTerm Γ (σ ⇒ τ)
    
  data CTerm (Γ : Ctx) : VType → Set where
    VAL : ∀ {σ} → VTerm Γ σ → CTerm Γ σ
    FAIL : ∀ {σ} → CTerm Γ σ
    CHOOSE : ∀ {σ} → CTerm Γ σ → CTerm Γ σ → CTerm Γ σ
    IF_THEN_ELSE_ : ∀ {σ} → VTerm Γ bool → CTerm Γ σ → CTerm Γ σ → CTerm Γ σ
    _$_ : ∀ {σ τ} → VTerm Γ (σ ⇒ τ) → VTerm Γ σ → CTerm Γ τ
    PREC : ∀ {σ} → VTerm Γ nat →
           CTerm Γ σ →
           CTerm (σ ∷ nat ∷ Γ) σ → CTerm Γ σ
    LET_IN_ : ∀ {σ τ} → CTerm Γ σ → CTerm (σ ∷ Γ) τ → CTerm Γ τ

proj : {Γ : Ctx} → {σ : VType} → σ ∈ Γ → ⟦ Γ ⟧l → ⟦ σ ⟧v
proj (here' p) ρ rewrite p = proj₁ ρ
proj (there x) ρ = proj x (proj₂ ρ)


primrec : {t : Set} → ℕ → t → (ℕ → t → t) → t
primrec zero z s = z
primrec (suc n) z s = s n (primrec n z s)

primrecT : {t : Set} → ℕ → T t → (ℕ → t → T t) → T t
primrecT zero z s = z
primrecT (suc n) z s = lift (s n) (primrecT n z s)

----------------------------------------------------------------------
mutual
  ⟦_⟧t : {Γ : Ctx} → {σ : VType} → VTerm Γ σ → ⟦ Γ ⟧l → ⟦ σ ⟧v
  ⟦ TT ⟧t ρ = true
  ⟦ FF ⟧t ρ = false
  ⟦ ZZ ⟧t ρ = zero
  ⟦ SS t ⟧t ρ = suc (⟦ t ⟧t ρ)
  ⟦ ⟨ t , u ⟩ ⟧t ρ = ⟦ t ⟧t ρ , ⟦ u ⟧t ρ
  ⟦ FST p ⟧t ρ = proj₁ (⟦ p ⟧t ρ)
  ⟦ SND p ⟧t ρ = proj₂ (⟦ p ⟧t ρ)
  ⟦ VAR x ⟧t ρ = proj x ρ
  ⟦ LAM σ t ⟧t ρ = λ x → ⟦ t ⟧ (x , ρ)
  
  ⟦_⟧ : {Γ : Ctx} → {σ : VType} → CTerm Γ σ → ⟦ Γ ⟧l → T ⟦ σ ⟧v
  ⟦ VAL v ⟧ ρ = η (⟦ v ⟧t ρ)
  ⟦ FAIL ⟧ ρ = sfail
  ⟦ CHOOSE t u ⟧ ρ = sor (⟦ t ⟧ ρ) (⟦ u ⟧ ρ)
  ⟦ IF b THEN m ELSE n ⟧ ρ = (if ⟦ b ⟧t ρ then ⟦ m ⟧ else ⟦ n ⟧) ρ
  ⟦ PREC v m n ⟧ ρ = primrecT (⟦ v ⟧t ρ) (⟦ m ⟧ ρ) (λ x → λ y → ⟦ n ⟧ (y , x , ρ))
  ⟦ t $ u ⟧ ρ = ⟦ t ⟧t ρ (⟦ u ⟧t ρ)

  ⟦ LET m IN n ⟧ ρ = lift (λ x → ⟦ n ⟧ (x , ρ)) (⟦ m ⟧ ρ)

----------------------------------------------------------------------

natify : ∀ {Γ} → ℕ → VTerm Γ nat
natify zero = ZZ
natify (suc n) = SS (natify n)

-- binary relations are inequal, if there are pointwise inequalities
lemma-⇒-1 : (u₁ u₂ v₁ v₂ : VType) → ¬ u₁ ≡ v₁ → ¬ (u₁ ⇒ u₂ ≡ v₁ ⇒ v₂)
lemma-⇒-1 u₁ u₂ .u₁ .u₂ ¬q refl = ¬q refl

lemma-⇒-2 : (u₁ u₂ v₁ v₂ : VType) → ¬ u₂ ≡ v₂ → ¬ (u₁ ⇒ u₂ ≡ v₁ ⇒ v₂)
lemma-⇒-2 u₁ u₂ .u₁ .u₂ ¬q refl = ¬q refl

lemma-∏-1 : (u₁ u₂ v₁ v₂ : VType) → ¬ u₁ ≡ v₁ → ¬ (u₁ ∏ u₂ ≡ v₁ ∏ v₂)
lemma-∏-1 u₁ u₂ .u₁ .u₂ ¬q refl = ¬q refl

lemma-∏-2 : (u₁ u₂ v₁ v₂ : VType) → ¬ u₂ ≡ v₂ → ¬ (u₁ ∏ u₂ ≡ v₁ ∏ v₂)
lemma-∏-2 u₁ u₂ .u₁ .u₂ ¬q refl = ¬q refl

-- is ALL of this really required?
_≟_ : (u v : VType) → Dec (u ≡ v)
nat ≟ nat      = yes refl
nat ≟ bool     = no (λ ())
nat ≟ u ⇒ v    = no (λ ())
nat ≟ (u ∏ v)  = no (λ ())
bool ≟ nat     = no (λ ())
bool ≟ bool    = yes refl
bool ≟ u ⇒ v   = no (λ ())
bool ≟ (u ∏ v) = no (λ ())
u ⇒ u₁ ≟ nat = no (λ ())
u ⇒ u₁ ≟ bool = no (λ ())
u₁ ⇒ u₂ ≟ v₁ ⇒ v₂ with u₁ ≟ v₁ | u₂ ≟ v₂
u₁ ⇒ u₂ ≟ v₁ ⇒ v₂ | yes p | yes q rewrite p | q = yes refl
u₁ ⇒ u₂ ≟ v₁ ⇒ v₂ | yes p | no ¬q = no (lemma-⇒-2 u₁ u₂ v₁ v₂ ¬q)
u₁ ⇒ u₂ ≟ v₁ ⇒ v₂ | no ¬p | q = no (lemma-⇒-1 u₁ u₂ v₁ v₂ ¬p)
u₁ ⇒ u₂ ≟ (v₁ ∏ v₂) = no (λ ())
(u ∏ v) ≟ nat = no (λ ())
(u ∏ v) ≟ bool = no (λ ())
(u₁ ∏ u₂) ≟ v₁ ⇒ v₂ = no (λ ())
(u₁ ∏ u₂) ≟ (v₁ ∏ v₂) with u₁ ≟ v₁ | u₂ ≟ v₂
(u₁ ∏ u₂) ≟ (v₁ ∏ v₂) | yes p | yes q rewrite p | q = yes refl
(u₁ ∏ u₂) ≟ (v₁ ∏ v₂) | yes p | no ¬q = no (lemma-∏-2 u₁ u₂ v₁ v₂ ¬q)
(u₁ ∏ u₂) ≟ (v₁ ∏ v₂) | no ¬p | yes q = no (lemma-∏-1 u₁ u₂ v₁ v₂ ¬p)
(u₁ ∏ u₂) ≟ (v₁ ∏ v₂) | no ¬p | no ¬q = no (lemma-∏-1 u₁ u₂ v₁ v₂ ¬p) -- duplicates previous line


------------------------------------------------------------

lemma-<? : (Γ : Ctx) (τ : VType) (n : ℕ) →
           ¬ n < length Γ →
           ¬ suc n < length (τ ∷ Γ)
lemma-<? _ _ n p (s≤s q) = p q

_<?_ : (n : ℕ) (Γ : Ctx) → Dec (n < length Γ)
n <? [] = no (λ ())
zero <? (x ∷ Γ) = yes (s≤s z≤n)
suc n <? (x ∷ Γ) with n <? Γ
suc n <? (x ∷ Γ) | yes p = yes (s≤s p)
suc n <? (x ∷ Γ) | no ¬p = no (lemma-<? Γ x n ¬p)

varify :  {Γ : Ctx} (n : ℕ) {p : truncate (n <? Γ)} →
         VTerm Γ (lkp Γ (fromℕ≤ (extract (n <? Γ) {p})))
varify {Γ} n {p} = VAR (trace Γ (fromℕ≤ (extract (n <? Γ) {p})))


----------------------------------------------------------------------
-- Silly examples

pv0      = ⟦ VAL (LAM nat (VAL (varify 0))) ⟧ tt
--pv0-contra = ⟦ VAL (LAM nat (VAL (varify 1))) ⟧ tt
pv1        = ⟦ VAL (varify 0) ⟧ (1 , tt)
--pv1-contra = ⟦ VAL (varify 1) ⟧ (1 , tt)
pv2        = ⟦ IF (varify 2) THEN VAL (varify 0) ELSE VAL (varify 1) ⟧ (1 , 2 , false , tt)
pv3 : {Γ : Ctx} → ⟦ nat ∷ Γ ⟧l →  T ℕ
pv3        = ⟦ VAL (varify 0) ⟧

-- http://mazzo.li/posts/Lambda.html builds variable proofs during type checking
-- data Syntax : Set where
--   var : ℕ → Syntax
-- data Term {n} {Γ : Ctx n) : Type → Set where
--   var : ∀ {τ} (v : Fin n) → τ ≡ lookup v Γ → Term Γ τ

----------------------------------------------------------------------

p1 = ⟦ VAL (varify 0) ⟧ (1 , tt)
p2 = ⟦ IF TT THEN (VAL (SS ZZ)) ELSE VAL ZZ ⟧ tt
p3 = ⟦ (varify 0) $ (varify 1) ⟧ ( (λ x → η (x * x)) , (3 , tt) ) 
p4 = ⟦ VAL (SND ⟨ ZZ , TT ⟩ ) ⟧ tt
p5 = ⟦ LAM nat (VAL (SS (varify 0))) $ ZZ ⟧ tt
p6 = ⟦ PREC (natify 6) (VAL ZZ) ((LET VAL (varify 0) IN (VAL (varify 1)) )) ⟧ tt
p7 : ℕ → T ℕ
p7 n  = ⟦ PREC (natify n) (VAL ZZ) (CHOOSE (VAL (varify 0)) (VAL (SS (SS (varify 0))))) ⟧ tt


add : ∀ {Γ} → VTerm Γ (nat ⇒ nat ⇒ nat)
add = (LAM nat (
          VAL (LAM nat
               (PREC (varify 0)
                     (VAL (varify 1))
                     (VAL (SS (varify 0)))))))
p-add-3-4 = ⟦ LET add $ varify 1 IN varify 0 $ varify 1 ⟧ (3 , (4 , tt))

mul : ∀ {Γ} → VTerm Γ (nat ⇒ nat ⇒ nat)
mul = (LAM nat (
          VAL (LAM nat
               (PREC (varify 0)
                     (VAL ZZ)
                     (LET add $ varify 0 IN
                          (
                               ( varify 0
                                    $ varify 4 )))))))
p-mul-3-4 = ⟦ LET mul $ natify 3 IN varify 0 $ natify 4 ⟧ tt



