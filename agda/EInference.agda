{-# OPTIONS --type-in-type #-}

module EInference where

open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; trans ; cong ; subst)

open import ELanguage
open import ESemantics
open import Exception
open import Finiteness
open import GradedMonad
open import OrderedMonoid
open GradedMonad.GradedMonad ExcEffGM
open OrderedMonoid.OrderedMonoid ExcEffOM

-----------------------------------------------------------
-- effect erasure


mutual
  erase≤V : {σ τ : VType} → σ ≤V τ → erase-vtype σ ≡ erase-vtype τ
  erase≤V st-refl = refl
  erase≤V (st-trans p p') = trans (erase≤V p) (erase≤V p')
  erase≤V (st-prod p p') rewrite erase≤V p | erase≤V p' = refl
  erase≤V (st-func p q) rewrite erase≤V p | erase≤C q = refl

  erase≤C : {σ τ : CType} → σ ≤C τ → erase-ctype σ ≡ erase-ctype τ
  erase≤C (st-comp _ p) = cong // (erase≤V p)



mutual
  erase-vterm : {Γ : Ctx} {σ : VType} → VTerm Γ σ → vTerm Γ (erase-vtype σ)
  erase-vterm TT = TT
  erase-vterm FF = FF
  erase-vterm ZZ = ZZ
  erase-vterm (SS t) = SS (erase-vterm t)
  erase-vterm ⟨ t , t' ⟩ = ⟨ erase-vterm t , erase-vterm t' ⟩ 
  erase-vterm (FST t) = FST (erase-vterm t)
  erase-vterm (SND t) = SND (erase-vterm t)
  erase-vterm (VAR x) = VAR x
  erase-vterm (LAM σ t) = LAM σ (erase-cterm t)
  erase-vterm {Γ} (VCAST t p) = subst (vTerm Γ) (erase≤V p) (erase-vterm t)

  erase-cterm : {Γ : Ctx} {τ : CType} → CTerm Γ τ → cTerm Γ (erase-ctype τ)
  erase-cterm (VAL x) = VAL (erase-vterm x)
  erase-cterm FAIL = FAIL
  erase-cterm (TRY t WITH t') = TRY erase-cterm t WITH erase-cterm t'
  erase-cterm (IF x THEN t ELSE t') = IF erase-vterm x THEN erase-cterm t ELSE erase-cterm t'
  erase-cterm (f $ x) = erase-vterm f $ erase-vterm x
  erase-cterm (LET t IN t') = LET erase-cterm t IN erase-cterm t'
  erase-cterm {Γ} (CCAST t p) = subst (cTerm Γ) (erase≤C p) (erase-cterm t)

-----------------------------------------------------------
-- effect inference

mutual 
  infer-vtype : {Γ : Ctx} {σ : vType} → vTerm Γ σ → Maybe VType
  infer-vtype TT = just bool
  infer-vtype FF = just bool
  infer-vtype ZZ = just nat
  infer-vtype (SS t) = just nat
  infer-vtype ⟨ t , t' ⟩ with infer-vtype t | infer-vtype t'
  ... | just σ | just σ' = just (σ ∏ σ')
  ... | _      | _       = nothing
  infer-vtype (FST t) with infer-vtype t
  ... | just (σ ∏ _) = just σ
  ... | _            = nothing
  infer-vtype (SND t) with infer-vtype t
  ... | just (_ ∏ σ') = just σ'
  ... | _             = nothing
  infer-vtype {Γ} (VAR x) = just (lkp Γ (idx x))
  infer-vtype (LAM σ t) with infer-ctype t
  ... | just τ = just (σ ⇒ τ)
  ... | _      = nothing

  infer-ctype : {σ : cType} {Γ : Ctx} → cTerm Γ σ → Maybe CType
  infer-ctype (VAL x) with infer-vtype x
  ... | just σ = just (ok / σ)
  ... | _      = nothing
  infer-ctype FAIL = {!!} -- err / {!!}
  infer-ctype (TRY t WITH t') with infer-ctype t | infer-ctype t'
  ... | just τ | just τ' = τ ⊔C τ'
  ... | _      | _       = nothing
  infer-ctype (IF x THEN t ELSE t') with infer-ctype t | infer-ctype t'
  ... | just τ | just τ' = τ ⊔C τ'
  ... | _      | _       = nothing
  infer-ctype (f $ t) with infer-vtype f -- FIXME: should match argument too
  ... | just (σ ⇒ τ) = just τ
  ... | _            = nothing
  infer-ctype (LET t IN t') with infer-ctype t | infer-ctype t'
  ... | just (e / _) | just (e' / τ') = just (e · e' / τ')
  ... | _            | _              = nothing


{-
mutual  
  infer-vterm : {Γ : Ctx} {σ : vType} → (t : vTerm Γ σ) → VTerm Γ (infer-vtype t)
  infer-vterm TT = TT
  infer-vterm FF = FF
  infer-vterm ZZ = ZZ
  infer-vterm (SS t) = {!!} -- SS (infer-vterm t)
  infer-vterm ⟨ t , t' ⟩ = ⟨ infer-vterm t , infer-vterm t' ⟩
  infer-vterm (FST t) = {!!} -- FST (infer-vterm t)
  infer-vterm (SND t) = {!!} -- SND (infer-vterm t)
  infer-vterm (VAR x) = {!!} --VAR x
  infer-vterm (LAM σ t) = LAM σ (infer t)
  
  infer : {Γ : Ctx} {σ : cType} → (t : cTerm Γ σ) → CTerm Γ (infer-ctype t)
  infer (VAL x) = VAL (infer-vterm x)
  infer FAIL = FAIL
  infer (TRY t WITH t' ) = {!!} --TRY infer t WITH infer t'
  infer (IF x THEN t ELSE t') = {!!} --IF infer-vterm x THEN infer t ELSE infer t'
  infer (f $ x) = {!!} --infer-vterm f $ infer-vterm x
--  infer γ (PREC x c c') = PREC (infer-vterm γ x) (infer γ c) {!!} {!!}
  infer (LET t IN t') = {!!} --LET infer t IN infer t'

-}
