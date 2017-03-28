{-# OPTIONS --type-in-type #-}

module EInference where

open import Data.Unit
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality --using (_≡_ ; refl; trans ; cong ; subst)
--open Reveal_·_is_
open import Relation.Nullary

open import ELanguage
--open import ESemantics
open import Exception
open import Finiteness hiding (inspect)
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
  erase-cterm (FAIL σ) = FAIL σ
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
  infer-ctype (FAIL σ) = just (err / σ)
  infer-ctype (TRY t WITH t') with infer-ctype t | infer-ctype t'
  ... | just τ | just τ' = τ ⊹C τ'
  ... | _      | _       = nothing
{-  infer-ctype (TRY t WITH t') with infer-ctype t | infer-ctype t' 
  infer-ctype (TRY t WITH t') | just (e / σ) | just (e' / σ') with σ ⊔V σ' -- FIXME: shouldn't it be _⊹C_
  infer-ctype (TRY t WITH t') | just (e / σ) | just (e' / σ') | just v = just (e ⊔ e' / v)
  infer-ctype (TRY t WITH t') | just (e / σ) | just (e' / σ') | _ = nothing  
  infer-ctype (TRY t WITH t') | _            | _              = nothing-}
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


whatsthis : {e : Exc} (σ σ' : VType) {σ⊔σ' : VType} → (σ ⊔V σ') ≡ just σ⊔σ' → (e / σ) ≤C (e / σ⊔σ')
whatsthis σ σ' p = st-comp ⊑-refl (ubV σ σ' p)

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
  
  infer-cterm' {Γ} (FAIL σ) with infer-ctype {Γ = Γ} (FAIL σ)
  ... | _ = FAIL σ
  
  infer-cterm' (TRY t WITH t') with infer-ctype t | infer-cterm' t | infer-ctype t' | infer-cterm' t'
  infer-cterm' (TRY t WITH t') | just (e / σ) | u | just (e' / σ') | u' with σ ⊔V σ' | inspect (_⊔V_ σ) σ'
  infer-cterm' (TRY t WITH t') | just (e / σ) | u | just (e' / σ') | u' | just x | [ p ] = TRY CCAST u {!!} WITH CCAST u' {!!}
  -- following works for CTerm' Γ (e ⊔ e' / σ), that is if-else
  --  TRY  CCAST u (st-comp ⊑-refl (ubV σ σ' p))
  --  WITH CCAST u' (st-comp ⊑-refl (ubV σ' σ (trans (⊔V-sym σ' σ) p)))
  infer-cterm' (TRY t WITH t') | just (e / σ) | u | just (e' / σ') | u' | nothing | _ = tt
  infer-cterm' (TRY t WITH t') | just (_ / _) | _ | nothing | _ = tt
  infer-cterm' (TRY t WITH t') | nothing | _ | _ | _ = tt

  infer-cterm' (IF x THEN t ELSE t') with infer-vtype x | infer-vterm' x
  infer-cterm' (IF x THEN t ELSE t') | just nat | _ = tt
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' with infer-ctype t | infer-cterm' t
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | just τ | u with infer-ctype t' | infer-cterm' t'
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | just (e / σ) | u | just (e' / σ') | u' with σ ⊔V σ' | inspect (_⊔V_ σ) σ'
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | just (e / σ) | u | just (e' / σ') | u' | just ⊔σ | [ p ] =
    IF x' THEN CCAST u (st-comp ⊑-refl (ubV σ σ' p))
          ELSE CCAST u' (st-comp ⊑-refl (ubV σ' σ (trans (⊔V-sym σ' σ) p)))
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | just (e / σ) | u | just (e' / σ') | u' | nothing | _ = tt
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | just _ | u | nothing | u' = tt
  infer-cterm' (IF x THEN t ELSE t') | just bool | x' | nothing | u = tt
  infer-cterm' (IF x THEN t ELSE t') | just (_ ∏ _) | _ = tt
  infer-cterm' (IF x THEN t ELSE t') | just (_ ⟹ _) | _ = tt
  infer-cterm' (IF x THEN t ELSE t') | nothing | _ = tt
  
  infer-cterm' (f $ x) with infer-vtype f | infer-vterm' f | infer-vtype x | infer-vterm' x
  infer-cterm' (f $ x) | just nat | _ | _ | _ = tt
  infer-cterm' (f $ x) | just bool | _ | _ | _ = tt
  infer-cterm' (f $ x) | just (_ ∏ _) | _ | _ | _ = tt
  infer-cterm' (f $ x) | just (σ ⟹ τ) | f' | just σ' | x' with σ ≡V? σ' -- FIXME: CASTING?
  infer-cterm' (f $ x) | just (σ ⟹ τ) | f' | just .σ | x' | yes refl = f' $ x'
  infer-cterm' (f $ x) | just (σ ⟹ τ) | f' | just σ' | x' | no ¬p = tt
  infer-cterm' (f $ x) | just (_ ⟹ _) | _ | nothing | _ = tt  
  infer-cterm' (f $ x) | nothing | _ | _ | _ = tt
  
  infer-cterm' (LET t IN t') with infer-ctype t | infer-cterm' t | infer-ctype t' | infer-cterm' t'
  infer-cterm' (LET t IN t') | just (e / σ) | u | just (e' / σ') | u' = LET u IN {!u'!} -- FIXME: casting
  infer-cterm' (LET t IN t') | just (_ / _) | _ | nothing | _ = tt
  infer-cterm' (LET t IN t') | nothing | _ | _ | _ = tt
