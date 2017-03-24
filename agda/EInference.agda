{-# OPTIONS --type-in-type #-}

module EInference where

open import Data.Unit
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; trans ; cong ; subst)
open import Relation.Nullary

open import ELanguage
--open import ESemantics
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
  erase≤V st-bn = {!!}
  erase≤V st-refl = refl
  erase≤V (st-prod p p') rewrite erase≤V p | erase≤V p' = refl
  erase≤V (st-func p q) rewrite erase≤V p | erase≤C q = refl

  erase≤C : {σ τ : CType} → σ ≤C τ → erase-ctype σ ≡ erase-ctype τ
  erase≤C (st-comp _ p) = cong // (erase≤V p)



mutual
  erase-vterm : {Γ : Ctx} {σ : VType} → VTerm Γ (just σ) → vTerm Γ (erase-vtype σ)
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

  erase-cterm : {Γ : Ctx} {τ : CType} → CTerm Γ (just τ) → cTerm Γ (erase-ctype τ)
  erase-cterm (VAL x) = VAL (erase-vterm x)
  erase-cterm FAIL = FAIL
  erase-cterm (TRY t WITH t') = TRY erase-cterm t WITH erase-cterm t'
  erase-cterm (IF x THEN t ELSE t') = IF erase-vterm x THEN erase-cterm t ELSE erase-cterm t'
  erase-cterm (f $ x) = erase-vterm f $ erase-vterm x
  erase-cterm (LET t IN t') = LET erase-cterm t IN erase-cterm t'
  erase-cterm {Γ} (CCAST t p) = subst (cTerm Γ) (erase≤C p) (erase-cterm t)

-----------------------------------------------------------
-- effect inference

mutual -- refined type inference
  infer-vtype : {Γ : Ctx} {σ : vType} → vTerm Γ σ → Maybe VType
  infer-vtype TT = just bool
  infer-vtype FF = just bool
  infer-vtype ZZ = just nat
  infer-vtype (SS t) with  infer-vtype t
  ... | just nat = just nat
  ... | _        = nothing
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
  ... | just τ = just (σ ⟹ τ)
  ... | _      = nothing

  infer-ctype : {σ : cType} {Γ : Ctx} → cTerm Γ σ → Maybe CType
  infer-ctype (VAL x) with infer-vtype x
  ... | just σ = just (ok / σ)
  ... | _      = nothing
  infer-ctype FAIL = {!!} -- err / {!!}
--  infer-ctype (TRY t WITH t') with infer-ctype t | infer-ctype t'
--  ... | just τ | just τ' = τ ⊹C τ'
--  ... | _      | _       = nothing
  infer-ctype (TRY t WITH t') with infer-ctype t | infer-ctype t'
  infer-ctype (TRY t WITH t') | just (e / σ) | just (e' / σ') with σ ⊔V σ'
  infer-ctype (TRY t WITH t') | just (e / σ) | just (e' / σ') | just v = just (e ⊔ e' / v)
  infer-ctype (TRY t WITH t') | just (e / σ) | just (e' / σ') | _ = nothing  
  infer-ctype (TRY t WITH t') | _            | _       = nothing
  infer-ctype (IF x THEN t ELSE t') with infer-vtype x | infer-ctype t | infer-ctype t'
  ... | just bool | just τ | just τ' = τ ⊔C τ'
  ... | _         | _      | _       = nothing
  infer-ctype (f $ t) with infer-vtype f | infer-vtype t -- FIXME: should match argument too?
  infer-ctype (f $ t) | just (σ ⟹ τ) | just σ' with σ ≡V? σ' -- should we allow subtypes implicitly
  infer-ctype (f $ t) | just (σ ⟹ τ) | just σ' | yes p = just τ
  infer-ctype (f $ t) | just (σ ⟹ τ) | just σ' | no ¬p = nothing
  infer-ctype (f $ t) | _             | _ = nothing
  infer-ctype (LET t IN t') with infer-ctype t | infer-ctype t'
  ... | just (e / _) | just (e' / τ') = just (e · e' / τ')
  ... | _            | _              = nothing


------------------------------------------------------------------------

data infer-vtermTypeD {Γ : Ctx} {σ : vType} (t : vTerm Γ σ) : Maybe VType →  Set where
  nothing : infer-vtermTypeD {Γ} {σ} t nothing
  just : ∀ {τ} → VTerm' Γ τ → infer-vtermTypeD {Γ} {σ} t (just τ)

data infer-ctermTypeD {Γ : Ctx} {τ : cType} (t : cTerm Γ τ) : Maybe CType →  Set where
  nothing : infer-ctermTypeD {Γ} {τ} t nothing
  just : ∀ {τ'} → CTerm' Γ τ' → infer-ctermTypeD {Γ} {τ} t (just τ')

infer-vtermType : {Γ : Ctx} {σ : vType} (t : vTerm Γ σ) → Set
infer-vtermType {Γ} {_} t with infer-vtype t 
... | nothing = ⊤
... | just τ = VTerm' Γ τ

infer-ctermType : {Γ : Ctx} {τ : cType} (t : cTerm Γ τ) → Set
infer-ctermType {Γ} {_} t with infer-ctype t 
... | nothing = ⊤
... | just τ = CTerm' Γ τ

infer-if-else : {τ τ' ⊔τ : CType} → (_ : τ ⊔C τ' ≡ just ⊔τ) → {Γ : Ctx} (x : VTerm' Γ bool) (u : CTerm' Γ τ) (u' : CTerm' Γ τ') → CTerm' Γ ⊔τ
infer-if-else {τ} {τ'} {⊔τ} x u u' with τ ≤C? ⊔τ | τ' ≤C? ⊔τ
infer-if-else x u u' | yes p | yes q = {!IF x THEN (CCAST ? ?) ELSE (CCAST ? ?)!}
infer-if-else x u u' | yes p | no ¬p = {!!}
infer-if-else x u u' | no ¬p | q = {!!}

mutual -- refined term inference
  infer-vterm' : {Γ : Ctx} {σ : vType} (t : vTerm Γ σ) → infer-vtermType {Γ} {σ} t 
  infer-vterm' TT = TT
  infer-vterm' FF = FF
  infer-vterm' ZZ = ZZ
  infer-vterm' (SS t) with infer-vtype t | infer-vterm' t -- NOTE: infer-vtype & infer-vterm should be looked at the same time
  ... | just nat | u = SS u -- NOTE2: i.e. we simply cannot write infer-vterm t instead of u
  ... | just bool | _ = tt
  ... | just (_ ∏ _) | _ = tt
  ... | just (_ ⟹ _) | _ = tt
  ... | nothing | _ = tt
  infer-vterm' ⟨ t , t' ⟩ with infer-vtype t | infer-vterm' t | infer-vtype t' | infer-vterm' t'
  ... | just _  | u | just _  | u' = ⟨ u , u' ⟩
  ... | just _  | _ | nothing | _  = tt -- QUESTION: why the 'just' is mandatory here?
  ... | nothing | _ | _       | _  = tt
  infer-vterm' (FST t) with infer-vtype t | infer-vterm' t
  ... | just nat | _ = tt
  ... | just bool | _ = tt
  ... | just (_ ∏ _) | u = FST u
  ... | just (_ ⟹ _) | _ = tt
  ... | nothing | _ = tt
  infer-vterm' (SND t) with infer-vtype t | infer-vterm' t
  ... | just nat | _ = tt
  ... | just bool | _ = tt
  ... | just (_ ∏ _) | u = SND u
  ... | just (_ ⟹ _) | _ = tt
  ... | nothing | _ = tt
  infer-vterm' {Γ} (VAR x) = VAR (trace Γ (idx x))
  infer-vterm' (LAM σ t) with infer-ctype t | infer-cterm' t
  ... | just _ | u = LAM σ u
  ... | nothing | u = tt

  infer-cterm' :  {Γ : Ctx} {τ : cType} (t : cTerm Γ τ) → infer-ctermType {Γ} {τ} t
  infer-cterm' (VAL t) with infer-vtype t | infer-vterm' t
  ... | just _ | u = VAL u
  ... | nothing | u = tt
  infer-cterm' FAIL = {!!}
  infer-cterm' (TRY t WITH t') = {!!}
  infer-cterm' (IF x THEN t ELSE t') with infer-vtype x | infer-vterm' x
  infer-cterm' (IF x THEN t ELSE t') | just nat | _ = tt
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' with infer-ctype t | infer-cterm' t
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | just τ | u with infer-ctype t' | infer-cterm' t'
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | just τ | u | just τ' | u' with τ ⊔C τ'
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | just τ | u | just τ' | u' | just ⊔τ = infer-if-else {!!} x' u u'
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | just τ | u | just τ' | u' | nothing = tt

{-  infer-cterm' (IF x₂ THEN t ELSE t') | just bool | x' | just (e / σ) | u | just (e' / σ') | u' | just (e'' / σ'') with (e / σ) ≤C? (e'' / σ'')
  infer-cterm' (IF x₂ THEN t ELSE t') | just bool | x' | just (e / σ) | u | just (e' / σ') | u' | just (e'' / σ'') | yes p = IF x' THEN CCAST u {!p!} ELSE CCAST u' {!!}
  infer-cterm' (IF x₂ THEN t ELSE t') | just bool | x' | just (e / σ) | u | just (e' / σ') | u' | just (e'' / σ'') | no ¬p = {!!}
  infer-cterm' (IF x₂ THEN t ELSE t') | just bool | x' | just (e / σ) | u | just (e' / σ') | u' | nothing = tt-}
  {-
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | just (e / τ) | u | just (e' / τ') | u' | just (e'' / σ) with (e / τ ) ≤C? (e'' / σ) --= IF x' THEN CCAST u {!!} ELSE {!u'!}
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | just (e / τ) | u | just (e' / τ') | u' | just (e'' / σ) | yes p = IF x' THEN CCAST u {!p!} ELSE {!!}
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | just (e / τ) | u | just (e' / τ') | u' | just (e'' / σ) | no ¬p = {!!}
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | just τ | u | just τ' | u' | nothing = tt
  -}
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | just _ | u | nothing | u' = tt
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | nothing | u = tt
  infer-cterm' (IF x THEN t ELSE t') | just (_ ∏ _) | _ = tt
  infer-cterm' (IF x THEN t ELSE t') | just (_ ⟹ _) | _ = tt
  infer-cterm' (IF x THEN t ELSE t') | nothing | _ = tt
  infer-cterm' (f $ x) with infer-vtype f | infer-vterm' f | infer-vtype x | infer-vterm' x
  infer-cterm' (f $ x) | just nat | _ | _ | _ = tt
  infer-cterm' (f $ x) | just bool | _ | _ | _ = tt
  infer-cterm' (f $ x) | just (_ ∏ _) | _ | _ | _ = tt
  infer-cterm' (f $ x) | just (σ ⟹ τ) | f' | just σ' | x' with σ ≡V? σ'
  infer-cterm' (f $ x) | just (σ ⟹ τ) | f' | just .σ | x' | yes refl = f' $ x'
  infer-cterm' (f $ x) | just (σ ⟹ τ) | f' | just σ' | x' | no ¬p = tt
  infer-cterm' (f $ x) | just (_ ⟹ _) | _ | nothing | _ = tt  
  infer-cterm' (f $ x) | nothing | _ | _ | _ = tt
  infer-cterm' (LET t IN t') with infer-ctype t | infer-cterm' t | infer-ctype t' | infer-cterm' t'
  infer-cterm' (LET t IN t') | just (e / σ) | u | just (e' / σ') | u' = LET u IN {!u'!} -- FIXME: casting
  infer-cterm' (LET t IN t') | just (_ / _) | _ | nothing | _ = tt
  infer-cterm' (LET t IN t') | nothing | _ | _ | _ = tt

{-
infer-var : {σ σ' : VType} {Γ : Ctx} → (σ ∈ Γ) → Maybe (VTerm Γ (just σ'))
infer-var {σ} {σ'} x with σ ≡V? σ'
infer-var x | yes refl = just (VAR x)
... | _     = nothing


infer-if-else' : {σ σ' : VType} {e e' : Exc} {Γ : Ctx} → VTerm Γ (just bool) → CTerm Γ (just (e / σ)) → CTerm Γ (just (e' / σ')) → Maybe (CTerm Γ (just (e ⊔ e' / σ )))
infer-if-else' {σ} {σ'} x t t' with σ ≡V? σ'
infer-if-else' x t t' | yes refl = just (IF x THEN t ELSE t')
infer-if-else' x t t' | no _ = nothing

infer-if-else : {τ τ' : CType} {Γ : Ctx} → VTerm Γ (just bool) → CTerm Γ (just τ) → CTerm Γ (just τ') → Maybe (CTerm Γ (τ ⊔C τ'))
infer-if-else {e / σ} {e' / σ'} x t t' with σ ≡V? σ' | (e / σ) ⊔C (e' / σ')
infer-if-else {e / σ} {e' / .σ} x t t' | yes refl | just (ε / v) = {!!} --just (IF x THEN {!!} ELSE CCAST t' {!!})
... | _ | _      = nothing

infer-if-else3 : {τ τ' : CType} {Γ : Ctx} → VTerm Γ (just bool) → CTerm Γ (just τ) → CTerm Γ (just τ') → Maybe (CTerm Γ (τ ⊔C τ'))
infer-if-else3 {e / σ} {e' / σ'} x t t' with e / σ ⊔C e' / σ'
infer-if-else3 {e / σ} {e' / σ'} x t t' | just (ε / τ)  = {!!}
infer-if-else3 {e / σ} {e' / σ'} x t t' | nothing = nothing

infer-if-else4 : {τ τ' : CType} {Γ : Ctx} → VTerm Γ (just bool) → CTerm Γ (just τ) → CTerm Γ (just τ') → Maybe (CTerm Γ (τ ⊔C τ'))
infer-if-else4 {τ} {τ'} x t t'            with τ ⊔C τ'
infer-if-else4 {e / σ} {e' / σ'} x t t'   | just (e'' / σ'') with σ ≡V? σ'' | σ' ≡V? σ'' | e ≡E? e'' | e' ≡E? e''
infer-if-else4 {.e / .σ} {.e / .σ} {Γ}  x t t'          | just (e / σ)     | yes refl | yes refl   | yes refl | yes refl = just (subst (λ ε → CTerm Γ (just (ε / σ))) (⊔-itself e) (IF x THEN t ELSE t'))
infer-if-else4 {e / _} {e' / σ'} x t t'             | just (e'' / σ)   | _        | _  | _        | _  = nothing
infer-if-else4 x t t'                     | nothing  = nothing


infer-if-else2 : {τ τ' : CType} {Γ : Ctx} → VTerm Γ (just bool) → CTerm Γ (just τ) → CTerm Γ (just τ') → Maybe (CTerm Γ (τ ⊔C τ'))
infer-if-else2 {e / σ} {e' / σ'} x t t' with e ⊔ e' | σ ⊔V σ'
... | ε | just v = just (IF x THEN {!!} ELSE {!!})
... | _ | _      = nothing

infer-app : {σ σ' : VType} {τ : CType} {Γ : Ctx} → VTerm Γ (just (σ ⟹ τ)) → VTerm Γ (just σ') → Maybe (CTerm Γ (just τ))
infer-app {σ} {σ'} f x with σ ≡V? σ' -- FIXME: allow subtype application too
infer-app f x | yes refl = just (f $ x)
infer-app f x | no _     = nothing


mutual
  infer-vterm : {Γ : Ctx} {σ : vType} (t : vTerm Γ σ) → Maybe (VTerm Γ (infer-vtype t))
  infer-vterm TT = just TT
  infer-vterm FF = just FF
  infer-vterm ZZ = just ZZ
  infer-vterm (SS t) with infer-vtype t | infer-vterm t
  ... | just nat | just t' = just (SS t')
  ... | _        | _       = nothing
  infer-vterm ⟨ t , t' ⟩
    with infer-vtype t | infer-vterm t | infer-vtype t' | infer-vterm t'
  ... | just _ | just u | just _ | just u' = just ⟨ u , u' ⟩
  ... | _      | _      | _      | _       = nothing
  infer-vterm (FST t) with infer-vtype t | infer-vterm t
  ... | just (_ ∏ _) | just t' = just (FST t')
  ... | _            | _       = nothing
  infer-vterm (SND t) with infer-vtype t | infer-vterm t
  ... | just (_ ∏ _) | just t' = just (SND t')
  ... | _            | _       = nothing
  infer-vterm {Γ} (VAR {σ} x) with infer-vtype (VAR x)
  ... | just σ' = infer-var x
  ... | _      = nothing
  infer-vterm (LAM σ t) with infer-ctype t | infer-cterm t
  ... | just _ | just t' = just (LAM σ t')
  ... | _      | _       = nothing

  infer-cterm : {Γ : Ctx} {σ : cType} (t : cTerm Γ σ) → Maybe (CTerm Γ (infer-ctype t))
  infer-cterm (VAL t) with infer-vtype t | infer-vterm t
  ... | just _ | just u = just (VAL u)
  ... | _      | _       = nothing
  infer-cterm FAIL = {!!}
  infer-cterm (TRY t WITH t')
    with infer-ctype t | infer-cterm t | infer-ctype t' | infer-cterm t'
  infer-cterm (TRY t WITH t') | just (e / σ) | just u | just (e' / σ') | just u' with σ ≡V? σ'
  infer-cterm (TRY t WITH t') | just (e / σ) | just u | just (e' / .σ) | just u' | yes refl = just {!TRY ? WITH ?!}
  infer-cterm (TRY t WITH t') | just (e / σ) | just u | just (e' / σ') | just u' | _ = nothing
  infer-cterm (TRY t WITH t') | _      | _      | _      | _       = nothing
  infer-cterm (IF x THEN t ELSE t')
    with infer-vtype x | infer-vterm x |
         infer-ctype t | infer-cterm t | infer-ctype t' | infer-cterm t'
  ... | just bool | just x' | just (e / σ) | just u | just (e' / σ') | just u' = infer-if-else x' u u'
  ... | _         | _       | _      | _      | _      | _ = nothing
  infer-cterm (f $ x)
    with infer-vtype f | infer-vterm f | infer-vtype x | infer-vterm x
  ... | just (_ ⟹ _) | just f' | just _ | just x' = infer-app f' x'
  ... | _             | _       | _       | _       = nothing
  infer-cterm (LET t IN t')
    with infer-ctype t | infer-cterm t | infer-ctype t' | infer-cterm t'
  ... | just (e / σ) | just u | just (e' / σ') | just u' = just (LET u IN {!u'!}) -- FIXME: match context
  ... | _            | _      | _              | _       = nothing
-}
