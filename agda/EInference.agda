{-# OPTIONS --type-in-type #-}

module EInference where

open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; cong)

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
  erase-vtype : VType → vType
  erase-vtype nat = nat
  erase-vtype bool = bool
  erase-vtype (σ ∏ σ') = erase-vtype σ ∏ erase-vtype σ'
  erase-vtype (σ ⇒ σ') = erase-vtype σ ⇒ erase-ctype σ'

  erase-ctype : CType → cType
  erase-ctype (e / σ) = // (erase-vtype σ)

erase-ctx : Ctx → Context
erase-ctx [] = []
erase-ctx (σ ∷ Γ) = erase-vtype σ ∷ erase-ctx Γ

erase-var : {Γ : Ctx} {σ : VType} → σ ∈ Γ → erase-vtype σ ∈ erase-ctx Γ
erase-var (here' refl) = here
erase-var (there p) = there (erase-var p)

mutual
  erase-vterm : {Γ : Ctx} {σ : VType} → VTerm Γ σ → vTerm (erase-ctx Γ) (erase-vtype σ)
  erase-vterm TT = TT
  erase-vterm FF = FF
  erase-vterm ZZ = ZZ
  erase-vterm (SS t) = SS (erase-vterm t)
  erase-vterm ⟨ t , t' ⟩ = ⟨ erase-vterm t , erase-vterm t' ⟩ 
  erase-vterm (FST t) = FST (erase-vterm t)
  erase-vterm (SND t) = SND (erase-vterm t)
  erase-vterm (VAR x) = VAR (erase-var x)
  erase-vterm (LAM σ x) = LAM (erase-vtype σ) (erase x)
  erase-vterm (VCAST t p) = {!!}

  erase : {Γ : Ctx} {τ : CType} → CTerm Γ τ → cTerm (erase-ctx Γ) (erase-ctype τ)
  erase (VAL x) = VAL (erase-vterm x)
  erase FAIL = FAIL
  erase (TRY t WITH t') = TRY erase t WITH erase t'
  erase (IF x THEN t ELSE t') = IF erase-vterm x THEN erase t ELSE erase t'
  erase (f $ x) = erase-vterm f $ erase-vterm x
  erase (LET t IN t') = LET erase t IN erase t'
  erase (CCAST t p) = {!!}

-----------------------------------------------------------
-- effect inference

get-func-body : {γ : Context} {σ : vType} {τ : cType} → vTerm γ (σ ⇒ τ) → cTerm (σ ∷ γ) τ
get-func-body (FST t) = {!!} -- get-func-body t
get-func-body (SND t) = {!!}
get-func-body (VAR x) = {!!} -- what if outside world is impure?
get-func-body (LAM σ x) = x

infer-effect : {γ : Context} {σ : cType} → cTerm γ σ → Exc
infer-effect (VAL _) = ok
infer-effect FAIL = err
infer-effect (TRY t WITH t') = infer-effect t ⊔ infer-effect t'
infer-effect (IF _ THEN t ELSE t') = infer-effect t ⊔ infer-effect t'
infer-effect (f $ _) = {!!} --infer-effect (get-func-body f)
--infer-effect (PREC _ t t') = {!!}
infer-effect (LET t IN t') = infer-effect t · infer-effect t'

mutual
  infer-vtype : vType → VType -- needs cTerm?
  infer-vtype nat = nat
  infer-vtype bool = bool
  infer-vtype (σ ∏ σ') = infer-vtype σ ∏ infer-vtype σ'
  infer-vtype (t ⇒ t') = infer-vtype t ⇒ infer-ctype {t'} {!!}

  infer-ctype : {σ : cType} {γ : Context} → cTerm γ σ → CType
  infer-ctype {// σ} t = infer-effect t / infer-vtype σ

infer-ctx : Context → Ctx
infer-ctx [] = []
infer-ctx (σ ∷ γ) = infer-vtype σ ∷ infer-ctx γ

infer-var : {γ : Context} {σ : vType} → σ ∈ γ → infer-vtype σ ∈ infer-ctx γ
infer-var (here' refl) = here
infer-var (there p) = there (infer-var p)

mutual  
  infer-vterm : {γ : Context} {σ : vType} → vTerm γ σ → VTerm (infer-ctx γ) (infer-vtype σ)
  infer-vterm TT = TT
  infer-vterm FF = FF
  infer-vterm ZZ = ZZ
  infer-vterm (SS t) = SS (infer-vterm t)
  infer-vterm ⟨ t , t' ⟩ = ⟨ infer-vterm t , infer-vterm t' ⟩
  infer-vterm (FST t) = FST (infer-vterm t)
  infer-vterm (SND t) = SND (infer-vterm t)
  infer-vterm (VAR x) = VAR (infer-var x)
  infer-vterm (LAM σ x) = LAM (infer-vtype σ) {!!}

  infer-vterm' :  {γ : Context} {σ : vType} {τ : cType} → (t : vTerm γ (σ ⇒ τ)) → VTerm (infer-ctx γ) (infer-vtype σ ⇒ infer-ctype (get-func-body t))
  infer-vterm' = {!!}
  
  infer : {γ : Context} {σ : vType} → (t : cTerm γ (// σ)) → CTerm (infer-ctx γ) (infer-ctype t)
  infer (VAL x) = VAL (infer-vterm x)
  infer FAIL = FAIL
  infer (TRY t WITH t') = TRY infer t WITH infer t'
  infer (IF x THEN t ELSE t') = IF infer-vterm x THEN infer t ELSE infer t'
  infer (f $ x) = infer-vterm' f $ infer-vterm x --infer-vterm f $ infer-vterm x
--  infer γ (PREC x c c') = PREC (infer-vterm γ x) (infer γ c) {!!} {!!}
  infer (LET t IN t') = LET infer t IN infer t'


{-
data Infer (Γ : Ctx) (σ : CType) : cTerm (erase-ctx Γ) (erase-ctype σ) → Set where
  ok : (t : CTerm Γ σ) → Infer Γ σ (erase t)
--  bad : Infer Γ 
-}
