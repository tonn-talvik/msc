{-# OPTIONS --type-in-type #-}

module EInference where

open import Data.List
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
  erase≤V (st-trans p p₁) = trans (erase≤V p) (erase≤V p₁)
  erase≤V (st-prod p p₁) = {!!}
  erase≤V (st-func p x) = {!!}

  erase≤C : {σ τ : CType} → σ ≤C τ → erase-ctype σ ≡ erase-ctype τ
  erase≤C = {!!}



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
  erase-vterm (LAM σ t) = LAM σ (erase t)
  erase-vterm {Γ} (VCAST t p) = subst (vTerm Γ) (erase≤V p) (erase-vterm t)

  erase : {Γ : Ctx} {τ : CType} → CTerm Γ τ → cTerm Γ (erase-ctype τ)
  erase (VAL x) = VAL (erase-vterm x)
  erase FAIL = FAIL
  erase (TRY t WITH t') = TRY erase t WITH erase t'
  erase (IF x THEN t ELSE t') = IF erase-vterm x THEN erase t ELSE erase t'
  erase (f $ x) = erase-vterm f $ erase-vterm x
  erase (LET t IN t') = LET erase t IN erase t'
  erase (CCAST t p) = {!!}

-----------------------------------------------------------
-- effect inference
{-
get-func-body : {γ : Context} {σ : vType} {τ : cType} → vTerm γ (σ ⇒ τ) → cTerm (σ ∷ γ) τ
get-func-body (FST t) = {!!} -- get-func-body t
get-func-body (SND t) = {!!}
get-func-body (VAR x) = {!!} -- what if outside world is impure?
get-func-body (LAM σ x) = x
-}

infer-effect : {Γ : Ctx} {σ : cType} → cTerm Γ σ → Exc
infer-effect (VAL _) = ok
infer-effect FAIL = err
infer-effect (TRY t WITH t') = infer-effect t ⊔ infer-effect t'
infer-effect (IF _ THEN t ELSE t') = infer-effect t ⊔ infer-effect t'
infer-effect (f $ _) = {!!} --infer-effect (get-func-body f)
--infer-effect (PREC _ t t') = {!!}
infer-effect (LET t IN t') = infer-effect t · infer-effect t'

mutual 
  infer-vtype : {σ : vType} {Γ : Ctx} → vTerm Γ σ → VType
  infer-vtype TT = bool
  infer-vtype FF = bool
  infer-vtype ZZ = nat
  infer-vtype (SS t) = nat
  infer-vtype ⟨ t , t₁ ⟩ = infer-vtype t ∏ infer-vtype t₁
  infer-vtype (FST t) with infer-vtype t
  infer-vtype (FST t) | nat = {!!}
  infer-vtype (FST t) | bool = {!!}
  infer-vtype (FST t) | σ₁ ∏ σ₂ = σ₁
  infer-vtype (FST t) | σ₁ ⇒ x = {!!}
  infer-vtype (SND t) with infer-vtype t
  ... | σ = {!!}
  infer-vtype {Γ = Γ} (VAR x) = lkp Γ (idx x)
  infer-vtype {Γ = Γ} (LAM σ t) =  σ ⇒ infer-ctype {Γ = σ ∷ Γ} t

  infer-ctype : {σ : cType} {Γ : Ctx} → cTerm Γ σ → CType
  infer-ctype (VAL x) =  ok / infer-vtype x
  infer-ctype FAIL =  err / {!!}
  infer-ctype (TRY t WITH t₁) = {!!}
  infer-ctype (IF x THEN t ELSE t₁) with infer-ctype t | infer-ctype t₁ 
  ... | e / σ | e' / σ'  =  e ⊔ e' / {!!}
  infer-ctype (f $ t) with infer-vtype f 
  infer-ctype (f $ t) | nat = {!!}
  infer-ctype (f $ t) | bool = {!!}
  infer-ctype (f $ t) | σ₂ ∏ σ₃ = {!!}
  infer-ctype (f $ t) | σ ⇒ e / τ = {!  kui σ ≤V infer-vtype t, siis ok, muidu vaja cast, aga see on infer'i juures või umbes nii !}
  infer-ctype (LET t IN t₁) = {!!} 


{-
mutual  
  infer-vterm : {Γ : Ctx} {σ : vType} → (t : vTerm Γ σ) → VTerm Γ (infer-vtype t)
  infer-vterm TT = TT
  infer-vterm FF = FF
  infer-vterm ZZ = ZZ
  infer-vterm (SS t) = SS (infer-vterm t)
  infer-vterm ⟨ t , t' ⟩ = ⟨ infer-vterm t , infer-vterm t' ⟩
  infer-vterm (FST t) = FST (infer-vterm t)
  infer-vterm (SND t) = SND (infer-vterm t)
  infer-vterm (VAR x) = VAR x
  infer-vterm (LAM σ t) = LAM σ (infer t)
  
  infer : {Γ : Ctx} {σ : cType} → (t : cTerm Γ σ) → CTerm Γ (infer-ctype t)
  infer (VAL x) = VAL (infer-vterm x)
  infer FAIL = FAIL
  infer (TRY t WITH t' ) = TRY infer t WITH infer t'
  infer (IF x THEN t ELSE t') = IF infer-vterm x THEN infer t ELSE infer t'
  infer (f $ x) = infer-vterm f $ infer-vterm x --infer-vterm f $ infer-vterm x
--  infer γ (PREC x c c') = PREC (infer-vterm γ x) (infer γ c) {!!} {!!}
  infer (LET t IN t') = LET infer t IN infer t'
-}

{-
data Infer (Γ : Ctx) (σ : CType) : cTerm (erase-ctx Γ) (erase-ctype σ) → Set where
  ok : (t : CTerm Γ σ) → Infer Γ σ (erase t)
--  bad : Infer Γ 
-}
