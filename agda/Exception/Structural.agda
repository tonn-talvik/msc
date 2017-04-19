module Structural where

open import Data.Bool hiding (T)
open import Data.Fin
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Exception
open import Finiteness
open import Grading
open Grading.OrderedMonoid ExcEffOM
open Grading.GradedMonad ExcEffGM
open import Raw
open import Refined
open import Semantics
open import Types


wkT : (Γ : Ctx) → (σ : VType) → Fin (suc (length Γ)) → Ctx
wkT Γ σ zero = σ ∷ Γ
wkT [] σ (suc x) = σ ∷ []
wkT (σ' ∷ Γ) σ (suc x) = σ' ∷ wkT Γ σ x 

wkvar : {Γ : Ctx} {σ : VType} →
        (x : Fin (suc (length Γ))) →
        {τ : VType} → τ ∈ Γ → τ ∈ wkT Γ σ x
wkvar zero y = there y
wkvar (suc x) (here' refl) = here' refl
wkvar (suc x) (there y) = there (wkvar x y) 


mutual
  wkV : {Γ : Ctx} {σ τ : VType} →
        (x : Fin (suc (length Γ))) →
        VTerm Γ τ → VTerm (wkT Γ σ x) τ
  wkV x TT = TT
  wkV x FF = FF
  wkV x ZZ = ZZ
  wkV x (SS t) = SS (wkV x t)
  wkV x ⟨ t , t' ⟩ = ⟨ wkV x t , wkV x t' ⟩
  wkV x (FST t) = FST (wkV x t)
  wkV x (SND t) = SND (wkV x t)
  wkV x (VAR x') = VAR (wkvar x x')
  wkV x (LAM σ t) = LAM σ (wkC (suc x) t)
  wkV x (VCAST t p) = VCAST (wkV x t) p

  
  wkC : {Γ : Ctx} {σ : VType} {τ : CType} →
        (x : Fin (suc (length Γ))) →
        CTerm Γ τ → CTerm (wkT Γ σ x) τ
  wkC x (VAL y) = VAL (wkV x y) 
  wkC x (FAIL σ) = FAIL σ
  wkC x (TRY t WITH t') = TRY (wkC x t) WITH (wkC x t')
  wkC x (IF b THEN t ELSE t') = IF (wkV x b) THEN (wkC x t) ELSE (wkC x t')
  wkC x (t $ u) = wkV x t $ wkV x u
  wkC x (PREC y t t' p) = PREC (wkV x y) (wkC x t) (wkC (suc (suc x)) t') p
  wkC x (LET t IN t') = LET (wkC x t) IN (wkC (suc x) t')
  wkC x (CCAST t p) = CCAST (wkC x t) p 

wk : {Γ : Ctx} → ⟪ Γ ⟫x →
     {σ : VType} → ⟪ σ ⟫v →
     (x : Fin (suc (length Γ))) → ⟪ wkT Γ σ x ⟫x 
wk ρ v zero = v , ρ
wk {[]} tt v (suc x) = v , tt
wk {_ ∷ _} (w , ρ) v (suc x) = w , wk ρ v x

lemmaVar : {Γ : Ctx} (ρ : ⟪ Γ ⟫x) →
           {σ : VType} (v : ⟪ σ ⟫v) →
           (x : Fin (suc (length Γ))) →
           {τ : VType} (y : τ ∈ Γ) →
           proj (wkvar x y) (wk ρ v x) ≡ proj y ρ
lemmaVar ρ v zero y = refl
lemmaVar ρ v (suc x) (here' refl) = refl
lemmaVar (_ , ρ) v (suc x) (there y) = lemmaVar ρ v x y

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v w z} → x ≡ y → u ≡ v → w ≡ z → f x u w ≡ f y v z
cong₃ f refl refl refl = refl


mutual 
  lemmaV : {Γ : Ctx} (ρ : ⟪ Γ ⟫x) →
           {σ : VType} (v : ⟪ σ ⟫v) →
           (x : Fin (suc (length Γ))) →
           {τ : VType} (t : VTerm Γ τ) →
           ⟦ wkV x t ⟧v (wk ρ v x) ≡ ⟦ t ⟧v ρ
  lemmaV ρ v x TT = refl
  lemmaV ρ v x FF = refl
  lemmaV ρ v x ZZ = refl
  lemmaV ρ v x (SS t) = cong suc (lemmaV ρ v x t)
  lemmaV ρ v x ⟨ t , u ⟩ = cong₂ _,_ (lemmaV ρ v x t) (lemmaV ρ v x u)
  lemmaV ρ v x (FST t) = cong proj₁ (lemmaV ρ v x t)
  lemmaV ρ v x (SND t) = cong proj₂ (lemmaV ρ v x t)
  lemmaV ρ v x (VAR y) = lemmaVar ρ v x y
  lemmaV ρ v x (LAM σ t) = funext (λ z → ⟦ wkC (suc x) t ⟧c (z , wk ρ v x))
                                  (λ z → ⟦ t ⟧c (z , ρ))
                                  (λ z → lemmaC (z , ρ) v (suc x) t)
  lemmaV ρ v x (VCAST t p) = cong (vcast p) (lemmaV ρ v x t)


  lemmaC : {Γ : Ctx} (ρ : ⟪ Γ ⟫x) →
           {σ : VType} (v : ⟪ σ ⟫v) →
           (x : Fin (suc (length Γ))) →
           {τ : CType} (t : CTerm Γ τ) →
           ⟦ wkC x t ⟧c (wk ρ v x) ≡ ⟦ t ⟧c ρ
  lemmaC ρ v x (VAL x') = cong η (lemmaV ρ v x x')
  lemmaC ρ v x (FAIL σ) = refl
  lemmaC ρ v x (TRY_WITH_ {e} {e'} t t') = cong₂ (or-else e e') (lemmaC ρ v x t) (lemmaC ρ v x t')
  lemmaC ρ v x (IF_THEN_ELSE_ {e} {e'} b t t')
    rewrite lemmaV ρ v x b | lemmaC ρ v x t | lemmaC ρ v x t' = refl
{- alternative without rewrite
  lemmaC ρ v x (IF_THEN_ELSE_ {e} {e'} b t t') =
    cong₃ (λ b t f → if b then (sub (lub e e') t) else (sub (lub-sym e' e) f))
          (lemmaV ρ v x b) (lemmaC ρ v x t) (lemmaC ρ v x t') -}
  lemmaC ρ v x (f $ x') rewrite lemmaV ρ v x f | lemmaV ρ v x x' = refl
  lemmaC ρ v x (PREC y t t' p) =
    cong₃ (λ n z s → primrecT n z s p)
          (lemmaV ρ v x y) (lemmaC ρ v x t)
          (funext (λ i acc → ⟦ wkC (suc (suc x)) t' ⟧c (acc , i , wk ρ v x))
                  (λ i acc → ⟦ t' ⟧c (acc , i , ρ))
                  (λ i → funext (λ acc → ⟦ wkC (suc (suc x)) t' ⟧c (acc , i , wk ρ v x))
                                 (λ acc → ⟦ t' ⟧c (acc , i , ρ))
                                 (λ acc → lemmaC (acc , i , ρ) v (suc (suc x)) t')))
  lemmaC ρ v x (LET_IN_ {e} {e'} t t') rewrite lemmaC ρ v x t =
    cong (λ f → bind {e} {e'} f (⟦ t ⟧c ρ))
         (funext (λ w → ⟦ wkC (suc x) t' ⟧c (w , wk ρ v x))
                 (λ w → ⟦ t' ⟧c (w , ρ))
                 (λ w → lemmaC (w , ρ) v (suc x) t'))
  lemmaC ρ v x (CCAST t p) = cong (ccast p) (lemmaC ρ v x t)

----------------------------------------------------------------------

ctrT : {Γ : Ctx} {σ : VType} → σ ∈ Γ → Ctx
ctrT {σ ∷ Γ} (here' refl) = σ ∷ σ ∷ Γ
ctrT {σ ∷ Γ} (there p) = σ ∷ ctrT p

ctrvar : {Γ : Ctx} {σ τ : VType} →
        (p : σ ∈ Γ) → τ ∈ ctrT p → τ ∈ Γ
ctrvar (here' refl) (here' refl) = here' refl
ctrvar (here' refl) (there q) = q
ctrvar (there p) (here' refl) = here' refl
ctrvar (there p) (there q) = there (ctrvar p q)

mutual
  ctrV : {Γ : Ctx} {σ : VType} {τ : VType} →
        (p : σ ∈ Γ) → VTerm (ctrT p) τ → VTerm Γ τ
  ctrV p TT = TT
  ctrV p FF = FF
  ctrV p ZZ = ZZ
  ctrV p (SS t) = SS (ctrV p t)
  ctrV p ⟨ t , t' ⟩ = ⟨ ctrV p t , ctrV p t' ⟩
  ctrV p (FST t) = FST (ctrV p t)
  ctrV p (SND t) = SND (ctrV p t)
  ctrV p (VAR x) = VAR (ctrvar p x)
  ctrV p (LAM σ t) = LAM σ (ctrC (there p) t)
  ctrV p (VCAST t q) = VCAST (ctrV p t) q
  
  ctrC : {Γ : Ctx} {σ : VType} {τ : CType} →
        (p : σ ∈ Γ) → CTerm (ctrT p) τ → CTerm Γ τ
  ctrC p (VAL x) = VAL (ctrV p x)
  ctrC p (FAIL σ) = FAIL σ
  ctrC p (TRY t WITH t') = TRY ctrC p t WITH ctrC p t'
  ctrC p (IF x THEN t ELSE t') = IF ctrV p x THEN ctrC p t ELSE ctrC p t'
  ctrC p (f $ x) = ctrV p f $ ctrV p x
  ctrC p (PREC x t t' q) = PREC (ctrV p x) (ctrC p t) (ctrC (there (there p)) t') q
  ctrC {Γ} p (LET t IN t') = LET ctrC p t IN ctrC (there p) t'
  ctrC p (CCAST t q) = CCAST (ctrC p t) q

ctr : {Γ : Ctx} → ⟪ Γ ⟫x →
      {σ : VType} → 
      (p : σ ∈ Γ) → ⟪ ctrT p ⟫x
ctr (w , ρ) (here' refl) = w , w , ρ
ctr (w , ρ) (there p) = w , ctr ρ p


lemma-ctr-var : {Γ : Ctx} (ρ : ⟪ Γ ⟫x) →
                {σ : VType} (p : σ ∈ Γ) →
                {τ : VType} (x : τ ∈ ctrT p) →
                proj x (ctr ρ p) ≡ proj (ctrvar p x) ρ
lemma-ctr-var ρ (here' refl) (here' refl) = refl
lemma-ctr-var ρ (here' refl) (there x) = refl
lemma-ctr-var ρ (there p) (here' refl) = refl
lemma-ctr-var (w , ρ) (there p) (there x) = lemma-ctr-var ρ p x

mutual
  lemma-ctrV : {Γ : Ctx} (ρ : ⟪ Γ ⟫x) →
               {σ : VType} (p : σ ∈ Γ) →
               {τ : VType} (t : VTerm (ctrT p) τ) →
               ⟦ t ⟧v (ctr ρ p) ≡ ⟦ ctrV p t ⟧v ρ
  lemma-ctrV ρ p TT = refl
  lemma-ctrV ρ p FF = refl
  lemma-ctrV ρ p ZZ = refl
  lemma-ctrV ρ p (SS t) = cong suc (lemma-ctrV ρ p t)
  lemma-ctrV ρ p ⟨ t , t' ⟩ = cong₂ _,_ (lemma-ctrV ρ p t) (lemma-ctrV ρ p t')
  lemma-ctrV ρ p (FST t) = cong proj₁ (lemma-ctrV ρ p t)
  lemma-ctrV ρ p (SND t) = cong proj₂ (lemma-ctrV ρ p t)
  lemma-ctrV ρ p (VAR x) = lemma-ctr-var ρ p x
  lemma-ctrV ρ p (LAM σ x) = funext (λ z → ⟦ x ⟧c (z , ctr ρ p))
                                      (λ z → ⟦ ctrC (there p) x ⟧c (z , ρ))
                                      (λ z → lemma-ctrC (z , ρ) (there p) x)
  lemma-ctrV ρ p (VCAST t q) = cong (vcast q) (lemma-ctrV ρ p t)
  
  lemma-ctrC : {Γ : Ctx} (ρ : ⟪ Γ ⟫x) →
               {σ : VType} (p : σ ∈ Γ) →
               {τ : CType} (t : CTerm (ctrT p) τ) →
               ⟦ t ⟧c (ctr ρ p) ≡ ⟦ ctrC p t ⟧c ρ
  lemma-ctrC ρ p (VAL x) = cong η (lemma-ctrV ρ p x)
  lemma-ctrC ρ p (FAIL σ) = refl
  lemma-ctrC ρ p (TRY_WITH_ {e} {e'} t t') = cong₂ (or-else e e') (lemma-ctrC ρ p t) (lemma-ctrC ρ p t')
  lemma-ctrC ρ p (IF x THEN t ELSE t') rewrite lemma-ctrV ρ p x | lemma-ctrC ρ p t | lemma-ctrC ρ p t' = refl
  lemma-ctrC ρ p (f $ x) rewrite lemma-ctrV ρ p f | lemma-ctrV ρ p x = refl
  lemma-ctrC ρ p (PREC x t t' q) = 
     cong₃ (λ n z s → primrecT n z s q)
          (lemma-ctrV ρ p x) (lemma-ctrC ρ p t)
          (funext (λ i acc → ⟦ t' ⟧c (acc , i , ctr ρ p))
                  (λ i acc → ⟦ ctrC (there (there p)) t' ⟧c (acc , i , ρ))
                  (λ i → funext (λ acc → ⟦ t' ⟧c (acc , i , ctr ρ p))
                                 (λ acc → ⟦ ctrC (there (there p)) t' ⟧c (acc , i , ρ))
                                 (λ acc → lemma-ctrC (acc , i , ρ) (there (there p)) t')))
  lemma-ctrC ρ p (LET_IN_ {e} {e'} t t') rewrite lemma-ctrC ρ p t =
    cong (λ f → bind {e} {e'} f (⟦ ctrC p t ⟧c ρ))
         (funext (λ w → ⟦ t' ⟧c (w , ctr ρ p))
                 (λ w → ⟦ ctrC (there p) t' ⟧c (w , ρ))
                 (λ w → lemma-ctrC (w , ρ) (there p) t'))
  lemma-ctrC ρ p (CCAST t q) = cong (ccast q) (lemma-ctrC ρ p t)


{-
mutual
  ctrV : {Γ : Ctx} {σ τ : VType} → VTerm (σ ∷ σ ∷ Γ) τ → VTerm (σ ∷ Γ) τ
  ctrV TT = TT
  ctrV FF = FF
  ctrV ZZ = ZZ
  ctrV (SS t) = SS (ctrV t)
  ctrV ⟨ t , t' ⟩ = ⟨ ctrV t , ctrV t' ⟩
  ctrV (FST t) = FST (ctrV t)
  ctrV (SND t) = SND (ctrV t)
  ctrV (VAR (here' x)) = VAR (here' x)
  ctrV (VAR (there x)) = VAR x
  ctrV {[]} {σ'} (LAM σ t) = LAM σ {!!}
  ctrV {x ∷ Γ} (LAM σ t) = {!!}
  ctrV (VCAST t p) = VCAST (ctrV t) p

  ctrC : {Γ : Ctx} {σ : VType} {τ : CType} → CTerm (σ ∷ σ ∷ Γ) τ → CTerm (σ ∷ Γ) τ
  ctrC (VAL x) = VAL (ctrV x)
  ctrC (FAIL σ) = FAIL σ
  ctrC (TRY t WITH t') = TRY ctrC t WITH ctrC t'
  ctrC (IF x THEN t ELSE t') = IF ctrV x THEN ctrC t ELSE ctrC t'
  ctrC (t $ t') = ctrV t $ ctrV t'
  ctrC (PREC x t t' p) = PREC (ctrV x) (ctrC t) {!!} p
  ctrC (LET t IN t') = LET ctrC t IN {!!}
  ctrC (CCAST t p) = CCAST (ctrC t) p
-}



