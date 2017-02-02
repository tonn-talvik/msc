module Language where

open import Relation.Nullary
open import Relation.Binary.Core using (_≡_ ; refl)

open import Data.Nat hiding (_≟_)
open import Data.Fin hiding (lift; _<_)
open import Data.List

open import Finiteness

------------------------------------------------------------  
infixr 30 _⇒_

data VType : Set where
  nat : VType
  bool : VType
  _⇒_ : VType → VType → VType
  _∏_ : VType → VType → VType
  

Ctx = List VType


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

------------------------------------------------------------

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


natify : ∀ {Γ} → ℕ → VTerm Γ nat
natify zero = ZZ
natify (suc n) = SS (natify n)
