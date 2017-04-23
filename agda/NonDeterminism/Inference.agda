module Inference where

open import Data.Fin hiding (_<_)
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Unit hiding (_≤?_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Raw
open import Refined
open import Types
open import NonDetBoundedVec
open import Finiteness
open import Grading
open Grading.OrderedMonoid ℕ*
open Grading.GradedMonad NDBV


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
  ... | just σ | just σ' = just (σ ● σ')
  ... | _      | _       = nothing
  infer-vtype Γ (FST t) with infer-vtype Γ t
  ... | just (σ ● _) = just σ
  ... | _            = nothing
  infer-vtype Γ (SND t) with infer-vtype Γ t
  ... | just (_ ● σ') = just σ'
  ... | _             = nothing
  infer-vtype Γ (VAR x) with x <? Γ
  infer-vtype Γ (VAR x) | yes p = just (lkp Γ (fromℕ≤ p))
  infer-vtype Γ (VAR x) | no ¬p = nothing
  infer-vtype Γ (LAM σ t) with infer-ctype (σ ∷ Γ) t
  ... | just τ = just (σ ⇒ τ)
  ... | _      = nothing

  infer-ctype : (Γ : Ctx) → cTerm → Maybe CType
  infer-ctype Γ (VAL x) with infer-vtype Γ x
  ... | just σ = just (1 / σ)
  ... | _      = nothing
  infer-ctype Γ (FAIL σ) = just (0 / σ)
  infer-ctype Γ (CHOOSE t t') with infer-ctype Γ t | infer-ctype Γ t'
  ... | just τ | just τ' = τ ⊹C τ'
  ... | _      | _       = nothing
  infer-ctype Γ (IF x THEN t ELSE t') with infer-vtype Γ x | infer-ctype Γ t | infer-ctype Γ t'
  ... | just bool | just τ | just τ' = τ ⊔C τ'
  ... | _         | _      | _       = nothing
  infer-ctype Γ (f $ t) with infer-vtype Γ f | infer-vtype Γ t
  infer-ctype Γ (f $ t) | just (σ ⇒ τ) | just σ' with σ' ≤V? σ
  infer-ctype Γ (f $ t) | just (σ ⇒ τ) | just σ' | yes _ = just τ
  infer-ctype Γ (f $ t) | just (_ ⇒ _) | just _  | no  _ = nothing
  infer-ctype Γ (f $ t) | _             | _       = nothing
  infer-ctype Γ (PREC x t t') with infer-vtype Γ x
  infer-ctype Γ (PREC x t t') | just nat with infer-ctype Γ t
  infer-ctype Γ (PREC x t t') | just nat | just (e / σ) with infer-ctype (σ ∷ nat ∷ Γ) t'
  infer-ctype Γ (PREC x t t') | just nat | just (e / σ) | just (e' / σ') with e · e' ≤? e | σ ≡V? σ'
  infer-ctype Γ (PREC x t t') | just nat | just (e / σ) | just (e' / σ') | yes _ | yes _ = just (e / σ)
  infer-ctype Γ (PREC x t t') | just nat | just (_ / _) | just (_  / _ ) | _     | _      = nothing
  infer-ctype Γ (PREC x t t') | just nat | just (_ / _) | _ = nothing
  infer-ctype Γ (PREC x t t') | just nat | _ = nothing
  infer-ctype Γ (PREC x t t') | _ = nothing
  infer-ctype Γ (LET t IN t') with infer-ctype Γ t 
  infer-ctype Γ (LET t IN t') | just (e / σ) with infer-ctype (σ ∷ Γ) t'
  infer-ctype Γ (LET t IN t') | just (e / σ) | just (e' / σ') = just (e · e' / σ')
  infer-ctype Γ (LET t IN t') | just (_ / _) | _              = nothing
  infer-ctype Γ (LET t IN t') | _            = nothing


------------------------------------------------------------------------

refined-vterm : (Γ : Ctx) (t : vTerm) → Set
refined-vterm Γ t with infer-vtype Γ t 
... | nothing = ⊤
... | just τ = VTerm Γ τ

refined-cterm : (Γ : Ctx) (t : cTerm) → Set
refined-cterm Γ t with infer-ctype Γ t 
... | nothing = ⊤
... | just τ = CTerm Γ τ


⊔V-subtype : {σ σ' : VType} {σ⊔σ' : VType} → σ ⊔V σ' ≡ just σ⊔σ' → {e : E} → e / σ ≤C e / σ⊔σ'
⊔V-subtype {σ} {σ'} p = st-comp ⊑-refl (ubV σ σ' p)

⊔V-subtype-sym : {σ σ' : VType} {σ⊔σ' : VType} → σ ⊔V σ' ≡ just σ⊔σ' → {e : E} → e / σ' ≤C e / σ⊔σ'
⊔V-subtype-sym {σ} {σ'} p = ⊔V-subtype (trans (⊔V-sym σ' σ) p)


mutual -- refined term inference
  refine-vterm : (Γ : Ctx) (t : vTerm) → refined-vterm Γ t 
  refine-vterm Γ TT = TT
  refine-vterm Γ FF = FF
  refine-vterm Γ ZZ = ZZ
  refine-vterm Γ (SS t) with infer-vtype Γ t | refine-vterm Γ t
  ... | just nat | u = SS u
  ... | just bool | _ = tt
  ... | just (_ ● _) | _ = tt
  ... | just (_ ⇒ _) | _ = tt
  ... | nothing | _ = tt
  refine-vterm Γ ⟨ t , t' ⟩ with infer-vtype Γ t | refine-vterm Γ t | infer-vtype Γ t' | refine-vterm Γ t'
  ... | just _  | u | just _  | u' = ⟨ u , u' ⟩
  ... | just _  | _ | nothing | _  = tt
  ... | nothing | _ | _       | _  = tt
  refine-vterm Γ (FST t) with infer-vtype Γ t | refine-vterm Γ t
  ... | just nat | _ = tt
  ... | just bool | _ = tt
  ... | just (_ ● _) | u = FST u
  ... | just (_ ⇒ _) | _ = tt
  ... | nothing | _ = tt
  refine-vterm Γ (SND t) with infer-vtype Γ t | refine-vterm Γ t
  ... | just nat | _ = tt
  ... | just bool | _ = tt
  ... | just (_ ● _) | u = SND u
  ... | just (_ ⇒ _) | _ = tt
  ... | nothing | _ = tt
  refine-vterm Γ (VAR x) with x <? Γ
  ... | yes p = VAR (trace Γ (fromℕ≤ p))
  ... | no _  = tt
  refine-vterm Γ (LAM σ t) with infer-ctype (σ ∷ Γ) t | refine-cterm (σ ∷ Γ) t
  ... | just _ | u = LAM σ u
  ... | nothing | u = tt


  refine-cterm : (Γ : Ctx) (t : cTerm) → refined-cterm Γ t
  refine-cterm Γ (VAL t) with infer-vtype Γ t | refine-vterm Γ t
  ... | just _ | u = VAL u
  ... | nothing | u = tt 
  refine-cterm Γ (FAIL σ) with infer-ctype Γ (FAIL σ)
  ... | _ = FAIL σ
  refine-cterm Γ (CHOOSE t t')
      with infer-ctype Γ t | refine-cterm Γ t |
           infer-ctype Γ t' | refine-cterm Γ t'
  ... | nothing | _ | _ | _ = tt
  ... | just _ | _ | nothing | _ = tt
  ... | just (e / σ) | u | just (e' / σ') | u'
          with σ ⊔V σ' | inspect (_⊔V_ σ) σ'
  ...     | nothing | _ = tt
  ...     | just _ | [ p ] =
    CHOOSE (CCAST u (⊔V-subtype p))
           (CCAST u' (⊔V-subtype-sym {σ} p))

  refine-cterm Γ (IF x THEN t ELSE t') with infer-vtype Γ x | refine-vterm Γ x
  refine-cterm Γ (IF x THEN t ELSE t') | just nat | _ = tt
  refine-cterm Γ (IF x THEN t ELSE t') | just bool | x' with infer-ctype Γ t | refine-cterm Γ t
  refine-cterm Γ (IF x THEN t ELSE t') | just bool | x' | just τ | u with infer-ctype Γ t' | refine-cterm Γ t'
  refine-cterm Γ (IF x THEN t ELSE t') | just bool | x' | just (e / σ) | u | just (e' / σ') | u' with σ ⊔V σ' | inspect (_⊔V_ σ) σ'
  refine-cterm Γ (IF x THEN t ELSE t') | just bool | x' | just (e / σ) | u | just (e' / σ') | u' | just ⊔σ | [ p ] =
    IF x' THEN CCAST u (⊔V-subtype p)
          ELSE CCAST u' (⊔V-subtype-sym {σ} p)
  refine-cterm Γ (IF x THEN t ELSE t') | just bool | x' | just (e / σ) | u | just (e' / σ') | u' | nothing | _ = tt
  refine-cterm Γ (IF x THEN t ELSE t') | just bool | x' | just _ | u | nothing | u' = tt
  refine-cterm Γ (IF x THEN t ELSE t') | just bool | x' | nothing | u = tt
  refine-cterm Γ (IF x THEN t ELSE t') | just (_ ● _) | _ = tt
  refine-cterm Γ (IF x THEN t ELSE t') | just (_ ⇒ _) | _ = tt
  refine-cterm Γ (IF x THEN t ELSE t') | nothing | _ = tt

  refine-cterm Γ (f $ x) with infer-vtype Γ f | refine-vterm Γ f | infer-vtype Γ x | refine-vterm Γ x
  refine-cterm Γ (f $ x) | just nat | _ | _ | _ = tt
  refine-cterm Γ (f $ x) | just bool | _ | _ | _ = tt
  refine-cterm Γ (f $ x) | just (_ ● _) | _ | _ | _ = tt
  refine-cterm Γ (f $ x) | just (σ ⇒ τ) | f' | just σ' | x' with σ' ≤V? σ
  refine-cterm Γ (f $ x) | just (σ ⇒ τ) | f' | just σ' | x' | yes p = f' $ VCAST x' p
  refine-cterm Γ (f $ x) | just (σ ⇒ τ) | f' | just σ' | x' | no ¬p = tt
  refine-cterm Γ (f $ x) | just (_ ⇒ _) | _ | nothing | _ = tt  
  refine-cterm Γ (f $ x) | nothing | _ | _ | _ = tt

  refine-cterm Γ (PREC x t t')  with infer-vtype Γ x | refine-vterm Γ x
  refine-cterm Γ (PREC x t t') | just nat | x' with infer-ctype Γ t | refine-cterm Γ t 
  refine-cterm Γ (PREC x t t') | just nat | x' | just (e / σ)  | u with infer-ctype (σ ∷ nat ∷ Γ) t' | refine-cterm (σ ∷ nat ∷ Γ) t'
  refine-cterm Γ (PREC x t t') | just nat | x' | just (e / σ) | u | just (e' / σ') | u' with e · e' ≤? e | σ ≡V? σ'
  refine-cterm Γ (PREC x t t') | just nat | x' | just (e / σ) | u | just (e' / .σ) | u' | yes p | yes refl = PREC x' u u' p
  refine-cterm Γ (PREC x t t') | just nat | _  | just (_ / _) | _ | just (_  / _ ) | _  | yes _ | no _     = tt
  refine-cterm Γ (PREC x t t') | just nat | _  | just (_ / _) | _ | just (_  / _ ) | _  | no  _ | _        = tt
  refine-cterm Γ (PREC x t t') | just nat | _  | just (_ / _) | _ | nothing | _ = tt
  refine-cterm Γ (PREC x t t') | just nat | _  | nothing | _ = tt
  refine-cterm Γ (PREC x t t') | just bool | _ = tt
  refine-cterm Γ (PREC x t t') | just (_ ● _) | _ = tt
  refine-cterm Γ (PREC x t t') | just (_ ⇒ _) | _ = tt
  refine-cterm Γ (PREC x t t') | nothing | _  = tt

  refine-cterm Γ (LET t IN t') with infer-ctype Γ t | refine-cterm Γ t 
  refine-cterm Γ (LET t IN t') | just (e / σ) | u with infer-ctype (σ ∷ Γ) t' | refine-cterm (σ ∷ Γ) t'
  refine-cterm Γ (LET t IN t') | just (e / σ) | u | just (e' / σ') | u' = LET u IN u'
  refine-cterm Γ (LET t IN t') | just (_ / _) | _ | nothing | _ = tt
  refine-cterm Γ (LET t IN t') | nothing | _  = tt

