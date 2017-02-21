module ELanguage where

open import Relation.Nullary
open import Relation.Binary.Core using (_≡_ ; refl)

open import Data.Nat hiding (_≟_)
open import Data.Fin hiding (lift; _<_)
open import Data.List
open import Data.String hiding (_≟_)

open import Finiteness
open import Exception

------------------------------------------------------------  
infixr 30 _⇒_/_

data VType : Set where
  nat : VType
  bool : VType
  _⇒_/_ : VType → E → VType → VType
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
    LAM : ∀ σ {ε τ} → CTerm (σ ∷ Γ) ε τ → VTerm Γ (σ ⇒ ε / τ)


  data CTerm (Γ : Ctx) : E → VType → Set where
    VAL : ∀ {σ} → VTerm Γ σ → CTerm Γ ok σ
    FAIL : ∀ {σ} → CTerm Γ err σ
    TRY_WITH_ : ∀ {ε σ} → CTerm Γ ε σ → CTerm Γ ε σ → CTerm Γ ε σ
    IF_THEN_ELSE_ : ∀ {σ ε} → VTerm Γ bool → CTerm Γ ε σ → CTerm Γ ε σ → CTerm Γ ε σ
    _$_ : ∀ {σ τ ε} → VTerm Γ (σ ⇒ ε / τ) → VTerm Γ σ → CTerm Γ ε τ
    PREC : ∀ {ε σ} → VTerm Γ nat →
           CTerm Γ ε σ →
           CTerm (σ ∷ nat ∷ Γ) ε σ → CTerm Γ ε σ
    LET_IN_ : ∀ {σ τ ε ε'} → CTerm Γ ε σ → CTerm (σ ∷ Γ) ε' τ → CTerm Γ (ε ·E ε') τ


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
