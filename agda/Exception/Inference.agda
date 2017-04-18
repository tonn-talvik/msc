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
  infer-vtype : Ctx → vTerm → Maybe VType
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
  ... | yes p = just (lkp Γ (fromℕ≤ p))
  ... | no ¬p = nothing
  infer-vtype Γ (LAM σ t) with infer-ctype (σ ∷ Γ) t
  ... | just τ = just (σ ⇒ τ)
  ... | _      = nothing

  infer-ctype : Ctx → cTerm → Maybe CType
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
  ...                          | yes _ = just τ
  ...                          | no  _ = nothing
  infer-ctype Γ (f $ t) | _ | _ = nothing
  infer-ctype Γ (PREC x t t')
      with infer-vtype Γ x
  ... | just nat with infer-ctype Γ t
  ...        | nothing = nothing
  ...        | just (e / σ) with infer-ctype (σ ∷ nat ∷ Γ) t'
  ...                       | nothing = nothing
  ...                       | just (e' / σ') with e · e' ⊑? e | σ ≡V? σ'
  ...                                        | yes _ | yes _ = just (e / σ)
  ...                                        | _     | _     = nothing
  infer-ctype Γ (PREC x t t') | _ = nothing
  infer-ctype Γ (LET t IN t') with infer-ctype Γ t 
  ... | nothing = nothing
  ... | just (e / σ) with infer-ctype (σ ∷ Γ) t'
  ...                | nothing        = nothing
  ...                | just (e' / σ') = just (e · e' / σ')


------------------------------------------------------------------------

refined-vterm : Ctx → vTerm → Set
refined-vterm Γ t with infer-vtype Γ t 
... | nothing = ⊤
... | just τ = VTerm Γ τ

refined-cterm : Ctx → cTerm → Set
refined-cterm Γ t with infer-ctype Γ t 
... | nothing = ⊤
... | just τ = CTerm Γ τ


⊔V-subtype : {σ σ' : VType} {σ⊔σ' : VType} → σ ⊔V σ' ≡ just σ⊔σ' → {e : E} → e / σ ≤C e / σ⊔σ'
⊔V-subtype {σ} {σ'} p = st-comp ⊑-refl (ubV σ σ' p)

⊔V-subtype-sym : {σ σ' : VType} {σ⊔σ' : VType} → σ ⊔V σ' ≡ just σ⊔σ' → {e : E} → e / σ' ≤C e / σ⊔σ'
⊔V-subtype-sym {σ} {σ'} p = ⊔V-subtype (trans (⊔V-sym σ' σ) p)


mutual
  refine-vterm : (Γ : Ctx) (t : vTerm) → refined-vterm Γ t 
  refine-vterm Γ TT = TT
  refine-vterm Γ FF = FF
  refine-vterm Γ ZZ = ZZ
  refine-vterm Γ (SS t) with infer-vtype Γ t | refine-vterm Γ t
  ... | just nat | u = SS u
  ... | just bool | _ = tt
  ... | just (_ ∏ _) | _ = tt
  ... | just (_ ⇒ _) | _ = tt
  ... | nothing | _ = tt
  refine-vterm Γ ⟨ t , t' ⟩
      with infer-vtype Γ t | refine-vterm Γ t |
           infer-vtype Γ t' | refine-vterm Γ t'
  ... | just _  | u | just _  | u' = ⟨ u , u' ⟩
  ... | just _  | _ | nothing | _  = tt
  ... | nothing | _ | _       | _  = tt
  refine-vterm Γ (FST t) with infer-vtype Γ t | refine-vterm Γ t
  ... | just nat | _ = tt
  ... | just bool | _ = tt
  ... | just (_ ∏ _) | u = FST u
  ... | just (_ ⇒ _) | _ = tt
  ... | nothing | _ = tt
  refine-vterm Γ (SND t) with infer-vtype Γ t | refine-vterm Γ t
  ... | just nat | _ = tt
  ... | just bool | _ = tt
  ... | just (_ ∏ _) | u = SND u
  ... | just (_ ⇒ _) | _ = tt
  ... | nothing | _ = tt
  refine-vterm Γ (VAR x) with x <? Γ
  ... | yes p = VAR (trace Γ (fromℕ≤ p))
  ... | no _  = tt
  refine-vterm Γ (LAM σ t)
      with infer-ctype (σ ∷ Γ) t | refine-cterm (σ ∷ Γ) t
  ... | just _ | u = LAM σ u
  ... | nothing | u = tt


  refine-cterm : (Γ : Ctx) (t : cTerm) → refined-cterm Γ t
  refine-cterm Γ (VAL t) with infer-vtype Γ t | refine-vterm Γ t
  ... | nothing | u = tt
  ... | just _ | u = VAL u

  refine-cterm Γ (FAIL σ) with infer-ctype Γ (FAIL σ)
  ... | _ = FAIL σ
  
  refine-cterm Γ (TRY t WITH t')
      with infer-ctype Γ t | refine-cterm Γ t |
           infer-ctype Γ t' | refine-cterm Γ t'
  ... | nothing      | _ | _              | _ = tt
  ... | just _       | _ | nothing        | _ = tt
  ... | just (e / σ) | u | just (e' / σ') | u'
           with σ ⊔V σ' | inspect (_⊔V_ σ) σ'
  ...      | nothing | _ = tt
  ...      | just _ | [ p ] =
      TRY  CCAST u (⊔V-subtype p)
      WITH CCAST u' (⊔V-subtype-sym {σ} p)

  refine-cterm Γ (IF x THEN t ELSE t')
      with infer-vtype Γ x | refine-vterm Γ x
  ... | nothing | _ = tt
  ... | just nat | _ = tt
  ... | just (_ ∏ _) | _ = tt
  ... | just (_ ⇒ _) | _ = tt
  ... | just bool | x'
           with infer-ctype Γ t | refine-cterm Γ t
  ...      | nothing | u = tt
  ...      | just (e  / σ) | u
                with infer-ctype Γ t' | refine-cterm Γ t'
  ...           | nothing | u' = tt
  ...           | just (e' / σ') | u'
                     with σ ⊔V σ' | inspect (_⊔V_ σ) σ'
  ...                | nothing | _     = tt
  ...                | just ⊔σ | [ p ] =
      IF x' THEN CCAST u (⊔V-subtype p)
            ELSE CCAST u' (⊔V-subtype-sym {σ} p)

  refine-cterm Γ (f $ x)
      with infer-vtype Γ f | refine-vterm Γ f |
           infer-vtype Γ x | refine-vterm Γ x
  ... | nothing   | _ | _ | _ = tt
  ... | just nat  | _ | _ | _ = tt
  ... | just bool | _ | _ | _ = tt
  ... | just (_ ∏ _) | _ | _ | _ = tt
  ... | just (_ ⇒ _) | _ | nothing | _ = tt  
  ... | just (σ ⇒ τ) | f' | just σ' | x' with σ' ≤V? σ
  ...                                     | no _  = tt
  ...                                     | yes p = f' $ VCAST x' p

  refine-cterm Γ (PREC x t t')  with infer-vtype Γ x | refine-vterm Γ x
  ... | nothing | _  = tt
  ... | just bool | _ = tt
  ... | just (_ ∏ _) | _ = tt
  ... | just (_ ⇒ _) | _ = tt
  ... | just nat | x'
          with infer-ctype Γ t | refine-cterm Γ t 
  ...     | nothing | _ = tt
  ...     | just (e / σ) | u
              with infer-ctype (σ ∷ nat ∷ Γ) t' |
                   refine-cterm (σ ∷ nat ∷ Γ) t'
  ...         | nothing | _ = tt
  ...         | just (e' / σ') | u' with e · e' ⊑? e | σ ≡V? σ'
  ...                               | no  _ | _    = tt
  ...                               | yes _ | no _ = tt
  refine-cterm Γ (PREC x t t')
      | just nat | x'
          | just (e / σ) | u
              | just (e' / .σ) | u' | yes p | yes refl = PREC x' u u' p

  refine-cterm Γ (LET t IN t') with infer-ctype Γ t | refine-cterm Γ t 
  ... | nothing | _  = tt
  ... | just (e / σ) | u with infer-ctype (σ ∷ Γ) t' |
                              refine-cterm (σ ∷ Γ) t'
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


--infer-corr : (Γ : Ctx) (t : cTerm) {τ : CType} → infer-ctype Γ t ≡ just τ → (t' : refined-cterm Γ t) → erase-cterm t' ≡ t -- leq
--infer-corr = {!!}


{-
xxx : (Γ : Ctx) → (t : vTerm) {σ : VType} → infer-vtype Γ t ≡ just σ → Set
xxx Γ t eq = {!erase-vterm (refine-vterm Γ t) ≡ t!}
corr-vtype : Ctx → vTerm → Set
corr-vtype Γ t with infer-vtype Γ t | inspect (infer-vtype Γ) t
corr-vtype Γ t | just σ' | Reveal_·_is_.[ eq ] = {!erase-vterm (refine-vterm Γ t) ≡ t!} --nwith refine-vterm Γ t
--...           | t' = erase-vterm t' ≡ t
... | nothing | _ = ⊤
-}

corr-vtype : Ctx → vTerm → Set
corr-vtype Γ t with infer-vtype Γ t | refine-vterm Γ t
... | just σ' | t' = erase-vterm t' ≡ t
... | nothing | _ = ⊤

corr-ctype : Ctx → cTerm → Set
corr-ctype Γ t with infer-ctype Γ t | refine-cterm Γ t
... | just τ' | t' = erase-cterm t' ≡ t
... | nothing | _ = ⊤
{-
help : (Γ : Ctx) (t : vTerm) → infer-vtype Γ t ≡ just nat → corr-vtype Γ (SS t)
help Γ t eq with infer-vtype Γ t | refine-vterm Γ t
help Γ t refl | just .nat | t' = {!!}
help Γ t eq | nothing | t' = tt


helper : (Γ : List VType) (t : vTerm) (w : Maybe VType) → w ≡ just nat →
  Reveal infer-vtype Γ · t is w →
  (w₁ : refined-vterm Γ t) →
  Reveal refine-vterm Γ · t is w₁ →
  corr-vtype Γ (SS t)
helper Γ t (just x) eq Reveal_·_is_.[ eq₁ ] w1 Reveal_·_is_.[ eq₂ ] = {!!}
helper Γ t nothing () p w1 q
mutual
  infer-vorr : (Γ : Ctx) (t : vTerm) → corr-vtype Γ t
  infer-vorr Γ TT with refine-vterm Γ TT
  ... | _ = refl
  infer-vorr Γ FF with refine-vterm Γ FF
  ... | _ = refl
  infer-vorr Γ ZZ with refine-vterm Γ ZZ
  ... | _ = refl
{ -  infer-vorr Γ (SS t) with infer-vtype Γ t | refine-vterm Γ t | inspect (infer-vtype Γ) t |  inspect (refine-vterm Γ) t
  infer-vorr Γ (SS t) | just nat | t' | Reveal_·_is_.[ eq ] | q = {!!} --cong SS (infer-vorr Γ {!t!})
  infer-vorr Γ (SS t) | just bool | t' | p  | q = tt
  infer-vorr Γ (SS t) | just (x ∏ x₁) | t' | p | q = tt
  infer-vorr Γ (SS t) | just (x ⇒ x₁) | t' | p | q = tt
  infer-vorr Γ (SS t) | nothing | t' | p | q = tt- }
  infer-vorr Γ (SS t) with infer-vtype Γ t | refine-vterm Γ t
  infer-vorr Γ (SS t) | just nat | t' = {!!}
  infer-vorr Γ (SS t) | just bool | t' = tt
  infer-vorr Γ (SS t) | just (x ∏ x₁) | t' = tt
  infer-vorr Γ (SS t) | just (x ⇒ x₁) | t' = tt
  infer-vorr Γ (SS t) | nothing | t' = tt
  infer-vorr Γ ⟨ t , t₁ ⟩ = {!!}
  infer-vorr Γ (FST t) = {!!}
  infer-vorr Γ (SND t) = {!!}
  infer-vorr Γ (VAR x) = {!!}
  infer-vorr Γ (LAM x x₁) = {!!}

  infer-corr : (Γ : Ctx) (t : cTerm) → corr-ctype Γ t
  infer-corr Γ t with infer-ctype Γ t | refine-cterm Γ t
  infer-corr Γ t | just τ' | t' = {!!}
  infer-corr Γ t | nothing | t' = tt
-}

--infer-corr : {Γ : Ctx} {τ : CType} (t : CTerm Γ τ) →
--             infer-ctype Γ (erase-cterm t) ≡ just τ → (t' : refined-cterm Γ (erase-cterm t)) → t' ≤C t
--infer-corr = ?

correct-type : (Γ : Ctx) {τ : CType} (t : CTerm Γ τ) → Set
correct-type Γ {τ} t with infer-ctype Γ (erase-cterm t)
... | just τ' = τ' ≤C τ
... | nothing = ⊤

{-
infer-correct : {Γ : Ctx} {τ : CType} (t : CTerm Γ τ) → correct-type Γ t
infer-correct {Γ} t with infer-ctype Γ (erase-cterm t) | refine-cterm Γ (erase-cterm t)
infer-correct t | just (e / σ) | t' = {!!}
infer-correct t | nothing | _ = tt
-}
