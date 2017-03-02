module ELanguage where

open import Relation.Nullary
open import Relation.Binary.Core using (_≡_ ; refl)

open import Data.Nat hiding (_≟_; _⊔_; _≤_)
open import Data.Fin hiding (lift; _<_; _≤_)
open import Data.List
open import Data.String hiding (_≟_)

open import Finiteness
open import Exception


infixl 90 _$_
infix  80 _/_
infixr 70 _⇒_
infix  60 _∏_

------------------------------------------------------------  

mutual
  data VType : Set where
    nat : VType
    bool : VType
    _∏_ : VType → VType → VType
    _⇒_ : VType → CType → VType

  data CType : Set where
    _/_ : E → VType → CType

-- subtyping of refined types
mutual
  data _≤_ : VType → VType → Set where
    st-refl : {σ : VType} → σ ≤ σ
    st-trans : {σ σ' τ : VType} → σ ≤ σ' → σ' ≤ τ → σ ≤ τ
    st-prod : {σ σ' τ τ' : VType} → σ ≤ σ' → τ ≤ τ' → σ ∏ τ ≤ σ' ∏ τ'
    st-func : {ε ε' : E} {σ σ' τ τ' : VType} →
              ε ⊑E ε' → σ ≤ σ' → ε / τ ⟪ ε' / τ' →
              σ ⇒ ε / τ ≤ σ' ⇒ ε' / τ'

  data _⟪_ : CType → CType → Set where
    st-comp : {ε ε' : E} {σ σ' : VType} → ε ⊑E ε' → σ ≤ σ' → ε / σ ⟪ ε' / σ'


Ctx = List VType




mutual
  data VTerm (Γ : Ctx) : VType → Set where
    TT FF : VTerm Γ bool
    ZZ : VTerm Γ nat
    SS : VTerm Γ nat → VTerm Γ nat
    ⟨_,_⟩ : ∀ {σ τ} → VTerm Γ σ → VTerm Γ τ → VTerm Γ (σ ∏ τ)
    FST : ∀ {σ τ} → VTerm Γ (σ ∏ τ) → VTerm Γ σ
    SND : ∀ {σ τ} → VTerm Γ (σ ∏ τ) → VTerm Γ τ
    VAR : ∀ {τ} → τ ∈ Γ → VTerm Γ τ
    LAM : ∀ σ {ε τ} → CTerm (σ ∷ Γ) (ε / τ) → VTerm Γ (σ ⇒ ε / τ)
    VCAST : ∀ {σ τ} → VTerm Γ σ → σ ≤ τ → VTerm Γ τ


  data CTerm (Γ : Ctx) : CType → Set where
    VAL : ∀ {σ} → VTerm Γ σ → CTerm Γ (ok / σ)
    FAIL : ∀ {σ} → CTerm Γ (err / σ)
    TRY_WITH_ : ∀ {ε ε' σ} → CTerm Γ (ε / σ) → CTerm Γ (ε' / σ) → CTerm Γ (ε ⊔ ε' / σ)
    IF_THEN_ELSE_ : ∀ {ε ε' σ} → VTerm Γ bool → CTerm Γ (ε / σ) → CTerm Γ (ε' / σ) → CTerm Γ (ε ⊔ ε' / σ)
    _$_ : ∀ {ε σ τ} → VTerm Γ (σ ⇒ ε / τ) → VTerm Γ σ → CTerm Γ (ε / τ)
    -- FIXME: allow primitive recursion to fail?
    PREC : ∀ {σ} → VTerm Γ nat →
           CTerm Γ (ok / σ) →
           CTerm (σ ∷ nat ∷ Γ) (ok / σ) → CTerm Γ (ok / σ)
    LET_IN_ : ∀ {ε ε' σ σ'} → CTerm Γ (ε / σ) → CTerm (σ ∷ Γ) (ε' / σ') → CTerm Γ (ε ·E ε' / σ')
    CCAST :  ∀ {ε ε' σ σ'} → CTerm Γ (ε / σ) → ε / σ ⟪ ε' / σ' → CTerm Γ (ε' / σ')


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
