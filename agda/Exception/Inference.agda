module Inference where

open import Data.Fin hiding (_<_)
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Raw
open import Types
open import Refined
open import Exception
open import Finiteness
open import Grading
open Grading.OrderedMonoid ExcEffOM
open Grading.GradedMonad ExcEffGM

lemma-<? : (Γ : Ctx) (σ : VType) (n : ℕ) →
           ¬ n < length Γ → ¬ suc n < length (σ ∷ Γ)
lemma-<? _ _ n p (s≤s q) = p q

_<?_ : (n : ℕ) (Γ : Ctx) → Dec (n < length Γ)
n <? [] = no (λ ())
zero <? (x ∷ Γ) = yes (s≤s z≤n)
suc n <? (x ∷ Γ) with n <? Γ
suc n <? (x ∷ Γ) | yes p = yes (s≤s p)
suc n <? (x ∷ Γ) | no ¬p = no (lemma-<? Γ x n ¬p)


-----------------------------------------------------------
-- effect inference

mutual -- refined type inference
  infer-vtype : (Γ : Ctx) → vTerm → Maybe VType
  infer-vtype Γ TT = just bool
  infer-vtype Γ FF = just bool
  infer-vtype Γ ZZ = just nat
  infer-vtype Γ (SS t) with  infer-vtype Γ t
  ... | just nat = just nat
  ... | _        = nothing
  infer-vtype Γ ⟨ t , t' ⟩ with infer-vtype Γ t | infer-vtype Γ t'
  ... | just σ | just σ' = just (σ ∏ σ')
  ... | _      | _       = nothing
  infer-vtype Γ (FST t) with infer-vtype Γ t
  ... | just (σ ∏ _) = just σ
  ... | _            = nothing
  infer-vtype Γ (SND t) with infer-vtype Γ t
  ... | just (_ ∏ σ') = just σ'
  ... | _             = nothing
  infer-vtype Γ (VAR x) with x <? Γ
  infer-vtype Γ (VAR x) | yes p = just (lkp Γ (fromℕ≤ p))
  infer-vtype Γ (VAR x) | no ¬p = nothing
  infer-vtype Γ (LAM σ t) with infer-ctype (σ ∷ Γ) t
  ... | just τ = just (σ ⇒ τ)
  ... | _      = nothing

  infer-ctype : (Γ : Ctx) → cTerm → Maybe CType
  infer-ctype Γ (VAL x) with infer-vtype Γ x
  ... | just σ = just (ok / σ)
  ... | _      = nothing
  infer-ctype Γ (FAIL σ) = just (err / σ)
  infer-ctype Γ (TRY t WITH t') with infer-ctype Γ t | infer-ctype Γ t'
  ... | just τ | just τ' = τ ⊹C τ'
  ... | _      | _       = nothing
  infer-ctype Γ (IF x THEN t ELSE t')
      with infer-vtype Γ x | infer-ctype Γ t | infer-ctype Γ t'
  ... | just bool | just τ | just τ' = τ ⊔C τ'
  ... | _         | _      | _       = nothing
  infer-ctype Γ (f $ t) with infer-vtype Γ f | infer-vtype Γ t
  ... | just (σ ⇒ τ) | just σ' with σ' ≤V? σ
  ...                           | yes _ = just τ
  ...                           | no  _ = nothing
  infer-ctype Γ (f $ t) | _ | _ = nothing
  infer-ctype Γ (PREC x t t')
      with infer-vtype Γ x
  ... | just nat with infer-ctype Γ t
  ...            | just (e / σ) with infer-ctype (σ ∷ nat ∷ Γ) t'
  ...                           | just (e' / σ') with e · e' ⊑? e | σ ≡V? σ'
  ...                                            | yes _ | yes _ = just (e / σ)
  ...                                            | _     | _     = nothing
  infer-ctype Γ (PREC x t t') | just nat | just (_ / _) | _ = nothing
  infer-ctype Γ (PREC x t t') | just nat | _ = nothing
  infer-ctype Γ (PREC x t t') | _ = nothing
  infer-ctype Γ (LET t IN t') with infer-ctype Γ t 
  ... | just (e / σ) with infer-ctype (σ ∷ Γ) t'
  ...                | just (e' / σ') = just (e · e' / σ')
  ...                | _              = nothing
  infer-ctype Γ (LET t IN t') | _            = nothing


------------------------------------------------------------------------

infer-vtermType : (Γ : Ctx) (t : vTerm) → Set
infer-vtermType Γ t with infer-vtype Γ t 
... | nothing = ⊤
... | just τ = VTerm Γ τ

infer-ctermType : (Γ : Ctx) (t : cTerm) → Set
infer-ctermType Γ t with infer-ctype Γ t 
... | nothing = ⊤
... | just τ = CTerm Γ τ


⊔V-subtype : {σ σ' : VType} {σ⊔σ' : VType} → σ ⊔V σ' ≡ just σ⊔σ' → {e : E} → e / σ ≤C e / σ⊔σ'
⊔V-subtype {σ} {σ'} p = st-comp ⊑-refl (ubV σ σ' p)

⊔V-subtype-sym : {σ σ' : VType} {σ⊔σ' : VType} → σ ⊔V σ' ≡ just σ⊔σ' → {e : E} → e / σ' ≤C e / σ⊔σ'
⊔V-subtype-sym {σ} {σ'} p = ⊔V-subtype (trans (⊔V-sym σ' σ) p)


mutual -- refined term inference
  infer-vterm : (Γ : Ctx) (t : vTerm) → infer-vtermType Γ t 
  infer-vterm Γ TT = TT
  infer-vterm Γ FF = FF
  infer-vterm Γ ZZ = ZZ
  infer-vterm Γ (SS t) with infer-vtype Γ t | infer-vterm Γ t
  ... | just nat | u = SS u
  ... | just bool | _ = tt
  ... | just (_ ∏ _) | _ = tt
  ... | just (_ ⇒ _) | _ = tt
  ... | nothing | _ = tt
  infer-vterm Γ ⟨ t , t' ⟩
      with infer-vtype Γ t | infer-vterm Γ t | infer-vtype Γ t' | infer-vterm Γ t'
  ... | just _  | u | just _  | u' = ⟨ u , u' ⟩
  ... | just _  | _ | nothing | _  = tt
  ... | nothing | _ | _       | _  = tt
  infer-vterm Γ (FST t) with infer-vtype Γ t | infer-vterm Γ t
  ... | just nat | _ = tt
  ... | just bool | _ = tt
  ... | just (_ ∏ _) | u = FST u
  ... | just (_ ⇒ _) | _ = tt
  ... | nothing | _ = tt
  infer-vterm Γ (SND t) with infer-vtype Γ t | infer-vterm Γ t
  ... | just nat | _ = tt
  ... | just bool | _ = tt
  ... | just (_ ∏ _) | u = SND u
  ... | just (_ ⇒ _) | _ = tt
  ... | nothing | _ = tt
  infer-vterm Γ (VAR x) with x <? Γ
  ... | yes p = VAR (trace Γ (fromℕ≤ p))
  ... | no _  = tt
  infer-vterm Γ (LAM σ t) with infer-ctype (σ ∷ Γ) t | infer-cterm (σ ∷ Γ) t
  ... | just _ | u = LAM σ u
  ... | nothing | u = tt


  infer-cterm : (Γ : Ctx) (t : cTerm) → infer-ctermType Γ t
  infer-cterm Γ (VAL t) with infer-vtype Γ t | infer-vterm Γ t
  ... | nothing | u = tt
  ... | just _ | u = VAL u

  infer-cterm Γ (FAIL σ) with infer-ctype Γ (FAIL σ)
  ... | _ = FAIL σ
  
  infer-cterm Γ (TRY t WITH t')
      with infer-ctype Γ t | infer-cterm Γ t | infer-ctype Γ t' | infer-cterm Γ t'
  ... | nothing      | _ | _              | _ = tt
  ... | just _       | _ | nothing        | _ = tt
  ... | just (e / σ) | u | just (e' / σ') | u' with σ ⊔V σ' | inspect (_⊔V_ σ) σ'
  ...                                          | nothing | _ = tt
  ...                                          | just _ | [ p ] =
      TRY  CCAST u (⊔V-subtype p)
      WITH CCAST u' (⊔V-subtype-sym {σ} p)

  infer-cterm Γ (IF x THEN t ELSE t')
      with infer-vtype Γ x | infer-vterm Γ x
  ... | nothing | _ = tt
  ... | just nat | _ = tt
  ... | just (_ ∏ _) | _ = tt
  ... | just (_ ⇒ _) | _ = tt
  ... | just bool | x' with infer-ctype Γ t | infer-cterm Γ t
  ...                  | nothing | u = tt
  ...                  | just (e  / σ) | u with infer-ctype Γ t' | infer-cterm Γ t'
  ...                                      | nothing | u' = tt
  ...                                      | just (e' / σ') | u' with σ ⊔V σ' | inspect (_⊔V_ σ) σ'
  ...                                                            | nothing | _     = tt
  ...                                                            | just ⊔σ | [ p ] =
      IF x' THEN CCAST u (⊔V-subtype p)
            ELSE CCAST u' (⊔V-subtype-sym {σ} p)

  infer-cterm Γ (f $ x)
      with infer-vtype Γ f | infer-vterm Γ f | infer-vtype Γ x | infer-vterm Γ x
  ... | nothing   | _ | _ | _ = tt
  ... | just nat  | _ | _ | _ = tt
  ... | just bool | _ | _ | _ = tt
  ... | just (_ ∏ _) | _ | _ | _ = tt
  ... | just (_ ⇒ _) | _ | nothing | _ = tt  
  ... | just (σ ⇒ τ) | f' | just σ' | x' with σ' ≤V? σ
  ...                                     | no _  = tt
  ...                                     | yes p = f' $ VCAST x' p



  infer-cterm Γ (PREC x t t')  with infer-vtype Γ x | infer-vterm Γ x
  ... | nothing | _  = tt
  ... | just bool | _ = tt
  ... | just (_ ∏ _) | _ = tt
  ... | just (_ ⇒ _) | _ = tt
  ... | just nat | x' with infer-ctype Γ t | infer-cterm Γ t 
  ...                 | nothing | _ = tt
  ...                 | just (e / σ) | u with infer-ctype (σ ∷ nat ∷ Γ) t' | infer-cterm (σ ∷ nat ∷ Γ) t'
  ...                                    | nothing | _ = tt
  ...                                    | just (e' / σ') | u' with e · e' ⊑? e | σ ≡V? σ'
  ...                                                          | no  _ | _        = tt
  ...                                                          | yes _ | no _     = tt
  infer-cterm Γ (PREC x t t')
      | just nat | x' | just (e / σ) | u | just (e' / .σ) | u' | yes p | yes refl = PREC x' u u' p

  infer-cterm Γ (LET t IN t') with infer-ctype Γ t | infer-cterm Γ t 
  ... | nothing | _  = tt
  ... | just (e / σ) | u with infer-ctype (σ ∷ Γ) t' | infer-cterm (σ ∷ Γ) t'
  ...                    | nothing        | _  = tt
  ...                    | just (e' / σ') | u' = LET u IN u'




-----------------------------------------------------------
-- effect erasure

{-
mutual
  erase-vtype : VType → vType
  erase-vtype nat = nat
  erase-vtype bool = bool
  erase-vtype (σ ∏ σ') = erase-vtype σ π erase-vtype σ'
  erase-vtype (σ ⇒ σ') = erase-vtype σ ⇒ erase-ctype σ'

  erase-ctype : CType → cType
  erase-ctype (e / σ) = // (erase-vtype σ)



mutual
  erase≤V : {σ τ : VType} → σ ≤V τ → erase-vtype σ ≡ erase-vtype τ
  erase≤V st-bn = {!!}
  erase≤V st-refl = refl
  erase≤V (st-prod p p') rewrite erase≤V p | erase≤V p' = refl
  erase≤V (st-func p q) rewrite erase≤V p | erase≤C q = refl

  erase≤C : {σ τ : CType} → σ ≤C τ → erase-ctype σ ≡ erase-ctype τ
  erase≤C (st-comp _ p) = cong // (erase≤V p)
-}


mutual
  erase-vterm : {Γ : Ctx} {σ : VType} → VTerm Γ σ → vTerm
  erase-vterm TT = TT
  erase-vterm FF = FF
  erase-vterm ZZ = ZZ
  erase-vterm (SS t) = SS (erase-vterm t)
  erase-vterm ⟨ t , t' ⟩ = ⟨ erase-vterm t , erase-vterm t' ⟩ 
  erase-vterm (FST t) = FST (erase-vterm t)
  erase-vterm (SND t) = SND (erase-vterm t)
  erase-vterm (VAR x) = VAR (toℕ (idx x))
  erase-vterm (LAM σ t) = LAM σ (erase-cterm t)
  erase-vterm (VCAST t p) = erase-vterm t

  erase-cterm : {Γ : Ctx} {τ : CType} → CTerm Γ τ → cTerm
  erase-cterm (VAL x) = VAL (erase-vterm x)
  erase-cterm (FAIL σ) = FAIL σ
  erase-cterm (TRY t WITH t') = TRY erase-cterm t WITH erase-cterm t'
  erase-cterm (IF x THEN t ELSE t') = IF erase-vterm x THEN erase-cterm t ELSE erase-cterm t'
  erase-cterm (f $ x) = erase-vterm f $ erase-vterm x
  erase-cterm (PREC x t t' p) = PREC (erase-vterm x) (erase-cterm t) (erase-cterm t')
  erase-cterm (LET t IN t') = LET erase-cterm t IN erase-cterm t'
  erase-cterm {Γ} (CCAST t p) = erase-cterm t

---------------------------------------------------------------------------------------------

--infer-corr : (Γ : Ctx) (t : cTerm) {τ : CType} → infer-ctype Γ t ≡ just τ → (t' : infer-ctermType Γ t) → erase t' ≡ t -- leq
--infer-corr = {!!}

--infer-corr : {Γ : Ctx} {τ : CType} (t : CTerm Γ τ) →
--             infer-ctype Γ (erase-cterm t) ≡ just τ → (t' : infer-ctermType Γ (erase-cterm t)) → t' ≤C t
--infer-corr = ?

correct-type : (Γ : Ctx) {τ : CType} (t : CTerm Γ τ) → Set
correct-type Γ {τ} t with infer-ctype Γ (erase-cterm t)
... | just τ' = τ' ≤C τ
... | nothing = ⊤

{-infer-corr : {Γ : Ctx} {τ : CType} (t : CTerm Γ τ) → correct-type Γ t
infer-corr {Γ} t with infer-ctype Γ (erase-cterm t) | infer-cterm Γ (erase-cterm t)
infer-corr t | just (e / σ) | t' = {!!}
infer-corr t | nothing | _ = tt
-}
