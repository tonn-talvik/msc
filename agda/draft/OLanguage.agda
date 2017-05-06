{-# OPTIONS --type-in-type #-}

module OLanguage where

open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; cong)

open import Exception
open import Finiteness
open import OrderedMonoid
open OrderedMonoid.OrderedMonoid ExcEffOM

infixl 90 _$_
infix  80 _/_
infixr 70 _⇒_
infix  60 _∏_


------------------------------------------------------------  

mutual -- value and computation types
  data VType : Set where
    nat : VType
    bool : VType
    _∏_ : VType → VType → VType
    _⇒_ : VType → CType → VType

  data CType : Set where
    _/_ : Exc → VType → CType


mutual -- subtyping of refined types
  data _≤V_ : VType → VType → Set where
    st-refl : {σ : VType} → σ ≤V σ
    st-trans : {σ σ' σ'' : VType} → σ ≤V σ' → σ' ≤V σ'' → σ ≤V σ''
    st-prod : {σ σ' τ τ' : VType} → σ ≤V σ' → τ ≤V τ' → σ ∏ τ ≤V σ' ∏ τ'
    st-func : {σ σ' : VType} {c c' : CType} →
              σ' ≤V σ → c ⟪ c' →
              σ ⇒ c ≤V σ' ⇒ c'

  data _⟪_ : CType → CType → Set where
    st-comp : {e e' : E} {σ σ' : VType} → e ⊑ e' → σ ≤V σ' → e / σ ⟪ e' / σ'


Ctx = List VType


mutual -- value and computation terms
  data VTerm (Γ : Ctx) : VType → Set where
    TT FF : VTerm Γ bool
    ZZ : VTerm Γ nat
    SS : VTerm Γ nat → VTerm Γ nat
    ⟨_,_⟩ : {σ σ' : VType} → VTerm Γ σ → VTerm Γ σ' → VTerm Γ (σ ∏ σ')
    FST : {σ σ' : VType} → VTerm Γ (σ ∏ σ') → VTerm Γ σ
    SND : {σ σ' : VType} → VTerm Γ (σ ∏ σ') → VTerm Γ σ'
    VAR : {σ : VType} → σ ∈ Γ → VTerm Γ σ
    LAM : (σ : VType) {ε : E} {τ : VType} → CTerm (σ ∷ Γ) (ε / τ) → VTerm Γ (σ ⇒ ε / τ)
--    LAM : (σ : VType) {τ : CType} → CTerm (σ ∷ Γ) τ → VTerm Γ (σ ⇒ τ)    
    VCAST : {σ σ' : VType} → VTerm Γ σ → σ ≤V σ' → VTerm Γ σ'

  data CTerm (Γ : Ctx) : CType → Set where
    VAL : {σ : VType} → VTerm Γ σ → CTerm Γ (ok / σ)
    FAIL : {σ : VType} → CTerm Γ (err / σ)
    TRY_WITH_ : ∀ {e e' σ} → CTerm Γ (e / σ) → CTerm Γ (e' / σ) → CTerm Γ (e ⊔ e' / σ)
    IF_THEN_ELSE_ : ∀ {e e' σ} → VTerm Γ bool → CTerm Γ (e / σ) → CTerm Γ (e' / σ) → CTerm Γ (e ⊔ e' / σ)
    _$_ : {σ : VType} {τ : CType} → VTerm Γ (σ ⇒ τ) → VTerm Γ σ → CTerm Γ τ
--    PREC : ∀ {e' e'' σ} → VTerm Γ nat → CTerm Γ (e'' / σ) →
--           CTerm (σ ∷ nat ∷ Γ) (e' / σ) → e'' · e' ⊑ e'' → CTerm Γ (e'' / σ)
    LET_IN_ : ∀ {e e' σ σ'} → CTerm Γ (e / σ) → CTerm (σ ∷ Γ) (e' / σ') → CTerm Γ (e · e' / σ')
    CCAST :  ∀ {e e' σ σ'} → CTerm Γ (e / σ) → e / σ ⟪ e' / σ' → CTerm Γ (e' / σ')

-----------------------------------------------------------
