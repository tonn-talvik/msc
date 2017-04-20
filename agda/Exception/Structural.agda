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

dropT : (Γ : Ctx) {σ : VType} (x : σ ∈ Γ) → Ctx
dropT .(x' ∷ xs) (here' {x'} {xs} x) = xs
dropT .(x' ∷ xs) (there {x'} {xs} x) = x' ∷ dropT xs x

wkvar : {Γ : Ctx} {σ : VType} (x : σ ∈ Γ) {τ : VType} → τ ∈ dropT Γ x → τ ∈ Γ
wkvar (here' refl) y = there y
wkvar (there x) (here' refl) = here' refl
wkvar (there x) (there y) = there (wkvar x y)


mutual
  wkV : {Γ : Ctx} {σ τ : VType} (x : σ ∈ Γ) →
        VTerm (dropT Γ x) τ → VTerm Γ τ
  wkV x TT = TT
  wkV x FF = FF
  wkV x ZZ = ZZ
  wkV x (SS t) = SS (wkV x t)
  wkV x ⟨ t , t' ⟩ = ⟨ wkV x t , wkV x t' ⟩
  wkV x (FST t) = FST (wkV x t)
  wkV x (SND t) = SND (wkV x t)
  wkV x (VAR x') = VAR (wkvar x x')
  wkV x (LAM σ t) = LAM σ (wkC (there x) t)
  wkV x (VCAST t p) = VCAST (wkV x t) p

  
  wkC : {Γ : Ctx} {σ : VType} {τ : CType} (x : σ ∈ Γ) →
        CTerm (dropT Γ x) τ → CTerm Γ τ
  wkC x (VAL y) = VAL (wkV x y) 
  wkC x (FAIL σ) = FAIL σ
  wkC x (TRY t WITH t') = TRY (wkC x t) WITH (wkC x t')
  wkC x (IF b THEN t ELSE t') = IF (wkV x b) THEN (wkC x t) ELSE (wkC x t')
  wkC x (t $ u) = wkV x t $ wkV x u
  wkC x (PREC y t t' p) = PREC (wkV x y) (wkC x t) (wkC (there (there x)) t') p
  wkC x (LET t IN t') = LET (wkC x t) IN (wkC (there x) t')
  wkC x (CCAST t p) = CCAST (wkC x t) p 


dropt : {Γ : Ctx} → ⟪ Γ ⟫x  → {σ : VType}  → (x : σ ∈ Γ) → 
     ⟪ dropT Γ x ⟫x 
dropt (_ , ρ) (here' refl) = ρ
dropt (v , ρ) (there x) = v , dropt ρ x

lemmaVar : {Γ : Ctx} → (ρ : ⟪ Γ ⟫x) → {σ : VType} 
  → (x : σ ∈ Γ) 
  → {τ : VType} → (y : τ ∈ dropT Γ x) → proj (wkvar x y) ρ ≡ proj y (dropt ρ x)
lemmaVar ρ (here' refl) y = refl
lemmaVar ρ (there x) (here' refl) = refl
lemmaVar {_ ∷ Γ} (_ , ρ) (there x) (there y) = lemmaVar ρ x y


cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v w z} → x ≡ y → u ≡ v → w ≡ z → f x u w ≡ f y v z
cong₃ f refl refl refl = refl


mutual 
  lemmaV : {Γ : Ctx} (ρ : ⟪ Γ ⟫x) →
           {σ : VType} (x : σ ∈ Γ) →
           {τ : VType} (t : VTerm (dropT Γ x) τ) →
           ⟦ wkV x t ⟧v ρ ≡ ⟦ t ⟧v (dropt ρ x)
  lemmaV ρ x TT = refl
  lemmaV ρ x FF = refl
  lemmaV ρ x ZZ = refl
  lemmaV ρ x (SS t) = cong suc (lemmaV ρ x t)
  lemmaV ρ x ⟨ t , u ⟩ = cong₂ _,_ (lemmaV ρ x t) (lemmaV ρ x u)
  lemmaV ρ x (FST t) = cong proj₁ (lemmaV ρ x t)
  lemmaV ρ x (SND t) = cong proj₂ (lemmaV ρ x t)
  lemmaV ρ x (VAR y) = lemmaVar ρ x y
  lemmaV ρ x (LAM σ t) = funext (λ z → ⟦ wkC (there x) t ⟧c (z , ρ))
                                (λ z → ⟦ t ⟧c (z , dropt ρ x))
                                (λ z → lemmaC (z , ρ) (there x) t)
  lemmaV ρ x (VCAST t p) = cong (vcast p) (lemmaV ρ x t)


  lemmaC : {Γ : Ctx} (ρ : ⟪ Γ ⟫x) →
           {σ : VType} (x : σ ∈ Γ) →
           {τ : CType} (t : CTerm (dropT Γ x) τ) →
           ⟦ wkC x t ⟧c ρ ≡ ⟦ t ⟧c (dropt ρ x)
  lemmaC ρ x (VAL x') = cong η (lemmaV ρ x x')
  lemmaC ρ x (FAIL σ) = refl
  lemmaC ρ x (TRY_WITH_ {e} {e'} t t') = cong₂ (or-else e e') (lemmaC ρ x t) (lemmaC ρ x t')
  lemmaC ρ x (IF_THEN_ELSE_ {e} {e'} b t t')
    rewrite lemmaV ρ x b | lemmaC ρ x t | lemmaC ρ x t' = refl
  lemmaC ρ x (f $ x') rewrite lemmaV ρ x f | lemmaV ρ x x' = refl
  lemmaC ρ x (PREC y t t' p) =
    cong₃ (λ n z s → primrecT n z s p)
          (lemmaV ρ x y) (lemmaC ρ x t)
          (funext (λ i acc → ⟦ wkC (there (there x)) t' ⟧c (acc , i , ρ))
                  (λ i acc → ⟦ t' ⟧c (acc , i , dropt ρ x))
                  (λ i → funext (λ acc → ⟦ wkC (there (there x)) t' ⟧c (acc , i , ρ))
                                 (λ acc → ⟦ t' ⟧c (acc , i , dropt ρ x))
                                 (λ acc → lemmaC (acc , i , ρ) (there (there x)) t')))
  lemmaC ρ x (LET_IN_ {e} {e'} t t') rewrite lemmaC ρ x t =
    cong (λ f → bind {e} {e'} f (⟦ t ⟧c (dropt ρ x)))
         (funext (λ w → ⟦ wkC (there x) t' ⟧c (w , ρ))
                 (λ w → ⟦ t' ⟧c (w , dropt ρ x))
                 (λ w → lemmaC (w , ρ) (there x) t'))
  lemmaC ρ x (CCAST t p) = cong (ccast p) (lemmaC ρ x t)

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



