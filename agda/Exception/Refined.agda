module Refined where

open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open Reveal_·_is_
open import Relation.Nullary

open import Types
open import Exception
open import Finiteness
open import Grading
open Grading.OrderedMonoid ExcEffOM


------------------------------------------------------------------------------

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
    LAM : (σ : VType) {τ : CType} → CTerm (σ ∷ Γ) τ → VTerm Γ (σ ⇒ τ)
    VCAST : {σ σ' : VType} → VTerm Γ σ → σ ≤V σ' → VTerm Γ σ'

  data CTerm (Γ : Ctx) : CType → Set where
    VAL : {σ : VType} → VTerm Γ σ → CTerm Γ (ok / σ)
    FAIL : (σ : VType) → CTerm Γ (err / σ)
    TRY_WITH_ : {e e' : E} {σ : VType} → CTerm Γ (e / σ) → CTerm Γ (e' / σ) → CTerm Γ (e ⊹ e' / σ)
    IF_THEN_ELSE_ : {e e' : E} {σ : VType} → VTerm Γ bool → CTerm Γ (e / σ) → CTerm Γ (e' / σ) → CTerm Γ (e ⊔ e' / σ)
    _$_ : {σ : VType} {τ : CType} → VTerm Γ (σ ⇒ τ) → VTerm Γ σ → CTerm Γ τ
    PREC : {e e' : E} {σ : VType} → VTerm Γ nat → CTerm Γ (e / σ) →
           CTerm (σ ∷ nat ∷ Γ) (e' / σ) → e · e' ⊑ e → CTerm Γ (e / σ)
    LET_IN_ : {e e' : E} {σ σ' : VType} → CTerm Γ (e / σ) → CTerm (σ ∷ Γ) (e' / σ') → CTerm Γ (e · e' / σ')
    CCAST :  {e e' : E} {σ σ' : VType} → CTerm Γ (e / σ) → e / σ ≤C e' / σ' → CTerm Γ (e' / σ')


