module Structural where

open import Data.Bool hiding (T)
open import Data.Fin
open import Data.List hiding (drop)
open import Data.Maybe
open import Data.Nat
open import Data.Product hiding (swap)
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

dropX : (Γ : Ctx) {σ : VType} (x : σ ∈ Γ) → Ctx
dropX .(x' ∷ xs) (here' {x'} {xs} x) = xs
dropX .(x' ∷ xs) (there {x'} {xs} x) = x' ∷ dropX xs x

wkvar : {Γ : Ctx} {σ : VType} (x : σ ∈ Γ) {σ' : VType} → σ' ∈ dropX Γ x → σ' ∈ Γ
wkvar (here' refl) y = there y
wkvar (there x) (here' refl) = here' refl
wkvar (there x) (there y) = there (wkvar x y)


mutual
  wkV : {Γ : Ctx} {σ σ' : VType} (x : σ ∈ Γ) →
        VTerm (dropX Γ x) σ' → VTerm Γ σ'
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
        CTerm (dropX Γ x) τ → CTerm Γ τ
  wkC x (VAL y) = VAL (wkV x y) 
  wkC x (FAIL σ) = FAIL σ
  wkC x (TRY t WITH t') = TRY (wkC x t) WITH (wkC x t')
  wkC x (IF b THEN t ELSE t') = IF (wkV x b) THEN (wkC x t) ELSE (wkC x t')
  wkC x (t $ u) = wkV x t $ wkV x u
  wkC x (PREC y t t' p) = PREC (wkV x y) (wkC x t) (wkC (there (there x)) t') p
  wkC x (LET t IN t') = LET (wkC x t) IN (wkC (there x) t')
  wkC x (CCAST t p) = CCAST (wkC x t) p 


drop : {Γ : Ctx} → ⟪ Γ ⟫X → {σ : VType} → (x : σ ∈ Γ) → ⟪ dropX Γ x ⟫X 
drop (_ , ρ) (here' refl) = ρ
drop (v , ρ) (there x) = v , drop ρ x

lemmaVar : {Γ : Ctx} → (ρ : ⟪ Γ ⟫X) → {σ : VType} 
  → (x : σ ∈ Γ) 
  → {σ' : VType} → (y : σ' ∈ dropX Γ x) → proj (wkvar x y) ρ ≡ proj y (drop ρ x)
lemmaVar ρ (here' refl) y = refl
lemmaVar ρ (there x) (here' refl) = refl
lemmaVar {_ ∷ Γ} (_ , ρ) (there x) (there y) = lemmaVar ρ x y


cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v w z} → x ≡ y → u ≡ v → w ≡ z → f x u w ≡ f y v z
cong₃ f refl refl refl = refl


mutual 
  lemma-wkV : {Γ : Ctx} (ρ : ⟪ Γ ⟫X) →
              {σ : VType} (x : σ ∈ Γ) →
              {σ' : VType} (t : VTerm (dropX Γ x) σ') →
              ⟦ wkV x t ⟧V ρ ≡ ⟦ t ⟧V (drop ρ x)
  lemma-wkV ρ x TT = refl
  lemma-wkV ρ x FF = refl
  lemma-wkV ρ x ZZ = refl
  lemma-wkV ρ x (SS t) = cong suc (lemma-wkV ρ x t)
  lemma-wkV ρ x ⟨ t , u ⟩ = cong₂ _,_ (lemma-wkV ρ x t) (lemma-wkV ρ x u)
  lemma-wkV ρ x (FST t) = cong proj₁ (lemma-wkV ρ x t)
  lemma-wkV ρ x (SND t) = cong proj₂ (lemma-wkV ρ x t)
  lemma-wkV ρ x (VAR y) = lemmaVar ρ x y
  lemma-wkV ρ x (LAM σ t) = funext (λ z → ⟦ wkC (there x) t ⟧C (z , ρ))
                                (λ z → ⟦ t ⟧C (z , drop ρ x))
                                (λ z → lemma-wkC (z , ρ) (there x) t)
  lemma-wkV ρ x (VCAST t p) = cong (vcast p) (lemma-wkV ρ x t)


  lemma-wkC : {Γ : Ctx} (ρ : ⟪ Γ ⟫X) →
              {σ : VType} (x : σ ∈ Γ) →
              {τ : CType} (t : CTerm (dropX Γ x) τ) →
              ⟦ wkC x t ⟧C ρ ≡ ⟦ t ⟧C (drop ρ x)
  lemma-wkC ρ x (VAL x') = cong η (lemma-wkV ρ x x')
  lemma-wkC ρ x (FAIL σ) = refl
  lemma-wkC ρ x (TRY_WITH_ {e} {e'} t t') = cong₂ (or-else e e') (lemma-wkC ρ x t) (lemma-wkC ρ x t')
  lemma-wkC ρ x (IF_THEN_ELSE_ {e} {e'} b t t')
    rewrite lemma-wkV ρ x b | lemma-wkC ρ x t | lemma-wkC ρ x t' = refl
  lemma-wkC ρ x (f $ x') rewrite lemma-wkV ρ x f | lemma-wkV ρ x x' = refl
  lemma-wkC ρ x (PREC y t t' p) =
    cong₃ (λ n z s → primrecT n z s p)
          (lemma-wkV ρ x y) (lemma-wkC ρ x t)
          (funext (λ i acc → ⟦ wkC (there (there x)) t' ⟧C (acc , i , ρ))
                  (λ i acc → ⟦ t' ⟧C (acc , i , drop ρ x))
                  (λ i → funext (λ acc → ⟦ wkC (there (there x)) t' ⟧C (acc , i , ρ))
                                 (λ acc → ⟦ t' ⟧C (acc , i , drop ρ x))
                                 (λ acc → lemma-wkC (acc , i , ρ) (there (there x)) t')))
  lemma-wkC ρ x (LET_IN_ {e} {e'} t t') rewrite lemma-wkC ρ x t =
    cong (λ f → bind {e} {e'} f (⟦ t ⟧C (drop ρ x)))
         (funext (λ w → ⟦ wkC (there x) t' ⟧C (w , ρ))
                 (λ w → ⟦ t' ⟧C (w , drop ρ x))
                 (λ w → lemma-wkC (w , ρ) (there x) t'))
  lemma-wkC ρ x (CCAST t p) = cong (ccast p) (lemma-wkC ρ x t)

----------------------------------------------------------------------

dupX : {Γ : Ctx} {σ : VType} → σ ∈ Γ → Ctx
dupX {σ ∷ Γ} (here' refl) = σ ∷ σ ∷ Γ
dupX {σ ∷ Γ} (there p) = σ ∷ dupX p

ctrvar : {Γ : Ctx} {σ σ' : VType} →
        (p : σ ∈ Γ) → σ' ∈ dupX p → σ' ∈ Γ
ctrvar (here' refl) (here' refl) = here' refl
ctrvar (here' refl) (there q) = q
ctrvar (there p) (here' refl) = here' refl
ctrvar (there p) (there q) = there (ctrvar p q)

mutual
  ctrV : {Γ : Ctx} {σ σ' : VType} (p : σ ∈ Γ) →
         VTerm (dupX p) σ' → VTerm Γ σ'
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
  
  ctrC : {Γ : Ctx} {σ : VType} {τ : CType} (p : σ ∈ Γ) →
         CTerm (dupX p) τ → CTerm Γ τ
  ctrC p (VAL x) = VAL (ctrV p x)
  ctrC p (FAIL σ) = FAIL σ
  ctrC p (TRY t WITH t') = TRY ctrC p t WITH ctrC p t'
  ctrC p (IF x THEN t ELSE t') = IF ctrV p x THEN ctrC p t ELSE ctrC p t'
  ctrC p (f $ x) = ctrV p f $ ctrV p x
  ctrC p (PREC x t t' q) = PREC (ctrV p x) (ctrC p t) (ctrC (there (there p)) t') q
  ctrC {Γ} p (LET t IN t') = LET ctrC p t IN ctrC (there p) t'
  ctrC p (CCAST t q) = CCAST (ctrC p t) q

dup : {Γ : Ctx} → ⟪ Γ ⟫X → {σ : VType} → (p : σ ∈ Γ) → ⟪ dupX p ⟫X
dup (w , ρ) (here' refl) = w , w , ρ
dup (w , ρ) (there p) = w , dup ρ p


lemma-ctr-var : {Γ : Ctx} (ρ : ⟪ Γ ⟫X) →
                {σ : VType} (p : σ ∈ Γ) →
                {σ' : VType} (x : σ' ∈ dupX p) →
                proj x (dup ρ p) ≡ proj (ctrvar p x) ρ
lemma-ctr-var ρ (here' refl) (here' refl) = refl
lemma-ctr-var ρ (here' refl) (there x) = refl
lemma-ctr-var ρ (there p) (here' refl) = refl
lemma-ctr-var (w , ρ) (there p) (there x) = lemma-ctr-var ρ p x

mutual
  lemma-ctrV : {Γ : Ctx} (ρ : ⟪ Γ ⟫X) →
               {σ : VType} (p : σ ∈ Γ) →
               {σ' : VType} (t : VTerm (dupX p) σ') →
               ⟦ t ⟧V (dup ρ p) ≡ ⟦ ctrV p t ⟧V ρ
  lemma-ctrV ρ p TT = refl
  lemma-ctrV ρ p FF = refl
  lemma-ctrV ρ p ZZ = refl
  lemma-ctrV ρ p (SS t) = cong suc (lemma-ctrV ρ p t)
  lemma-ctrV ρ p ⟨ t , t' ⟩ = cong₂ _,_ (lemma-ctrV ρ p t) (lemma-ctrV ρ p t')
  lemma-ctrV ρ p (FST t) = cong proj₁ (lemma-ctrV ρ p t)
  lemma-ctrV ρ p (SND t) = cong proj₂ (lemma-ctrV ρ p t)
  lemma-ctrV ρ p (VAR x) = lemma-ctr-var ρ p x
  lemma-ctrV ρ p (LAM σ t) = funext (λ z → ⟦ t ⟧C (z , dup ρ p))
                                    (λ z → ⟦ ctrC (there p) t ⟧C (z , ρ))
                                    (λ z → lemma-ctrC (z , ρ) (there p) t)
  lemma-ctrV ρ p (VCAST t q) = cong (vcast q) (lemma-ctrV ρ p t)
  
  lemma-ctrC : {Γ : Ctx} (ρ : ⟪ Γ ⟫X) →
               {σ : VType} (p : σ ∈ Γ) →
               {τ : CType} (t : CTerm (dupX p) τ) →
               ⟦ t ⟧C (dup ρ p) ≡ ⟦ ctrC p t ⟧C ρ
  lemma-ctrC ρ p (VAL x) = cong η (lemma-ctrV ρ p x)
  lemma-ctrC ρ p (FAIL σ) = refl
  lemma-ctrC ρ p (TRY_WITH_ {e} {e'} t t') = cong₂ (or-else e e') (lemma-ctrC ρ p t) (lemma-ctrC ρ p t')
  lemma-ctrC ρ p (IF x THEN t ELSE t') rewrite lemma-ctrV ρ p x | lemma-ctrC ρ p t | lemma-ctrC ρ p t' = refl
  lemma-ctrC ρ p (f $ x) rewrite lemma-ctrV ρ p f | lemma-ctrV ρ p x = refl
  lemma-ctrC ρ p (PREC x t t' q) = 
     cong₃ (λ n z s → primrecT n z s q)
          (lemma-ctrV ρ p x) (lemma-ctrC ρ p t)
          (funext (λ i acc → ⟦ t' ⟧C (acc , i , dup ρ p))
                  (λ i acc → ⟦ ctrC (there (there p)) t' ⟧C (acc , i , ρ))
                  (λ i → funext (λ acc → ⟦ t' ⟧C (acc , i , dup ρ p))
                                 (λ acc → ⟦ ctrC (there (there p)) t' ⟧C (acc , i , ρ))
                                 (λ acc → lemma-ctrC (acc , i , ρ) (there (there p)) t')))
  lemma-ctrC ρ p (LET_IN_ {e} {e'} t t') rewrite lemma-ctrC ρ p t =
    cong (λ f → bind {e} {e'} f (⟦ ctrC p t ⟧C ρ))
         (funext (λ w → ⟦ t' ⟧C (w , dup ρ p))
                 (λ w → ⟦ ctrC (there p) t' ⟧C (w , ρ))
                 (λ w → lemma-ctrC (w , ρ) (there p) t'))
  lemma-ctrC ρ p (CCAST t q) = cong (ccast q) (lemma-ctrC ρ p t)


---------------------------------------------------------------------------


swapX : {Γ : Ctx} {σ : VType} → σ ∈ Γ → Ctx
swapX {σ ∷ []} (here' x) = σ ∷ []
swapX {σ ∷ σ' ∷ Γ} (here' x) = σ' ∷ σ ∷ Γ
swapX {σ ∷ Γ} (there p) = σ ∷ swapX p

swapvar : {Γ : Ctx} {σ σ' : VType} (p : σ ∈ Γ) → σ' ∈ Γ → σ' ∈ swapX p
swapvar {σ ∷ []} (here' refl) (here' refl) = here' refl
swapvar {σ ∷ σ' ∷ Γ} (here' refl) (here' refl) = there (here' refl)
swapvar {σ ∷ []} (here' refl) (there x) = there x
swapvar {σ ∷ σ' ∷ Γ} (here' refl) (there (here' x)) = here' x
swapvar {σ ∷ σ' ∷ Γ} (here' refl) (there (there x)) = there (there x)
swapvar (there p) (here' x) = here' x
swapvar (there p) (there x) = there (swapvar p x)

swap : {Γ : Ctx} → ⟪ Γ ⟫X → {σ : VType} → (p : σ ∈ Γ) → ⟪ swapX p ⟫X
swap {_ ∷ []} (σ , ρ) (here' refl) = σ , tt
swap {_ ∷ _ ∷ _} (σ , σ' , ρ) (here' refl) = σ' , σ , ρ
swap (σ , ρ) (there p) = σ , swap ρ p

mutual
  swapV : {Γ : Ctx} {σ σ' : VType} (p : σ ∈ Γ) →
          VTerm Γ σ' → VTerm (swapX p) σ'
  swapV p TT = TT
  swapV p FF = FF
  swapV p ZZ = ZZ
  swapV p (SS t) = SS (swapV p t)
  swapV p ⟨ t , t' ⟩ = ⟨ swapV p t , swapV p t' ⟩
  swapV p (FST t) = FST (swapV p t)
  swapV p (SND t) = SND (swapV p t)
  swapV p (VAR x) = VAR (swapvar p x)
  swapV p (LAM σ t) = LAM σ (swapC (there p) t)
  swapV p (VCAST t q) = VCAST (swapV p t) q

  swapC : {Γ : Ctx} {σ : VType} {τ : CType} (p : σ ∈ Γ) →
          CTerm Γ τ → CTerm (swapX p) τ
  swapC p (VAL x) = VAL (swapV p x)
  swapC p (FAIL σ) = FAIL σ
  swapC p (TRY t WITH t') = TRY swapC p t WITH swapC p t'
  swapC p (IF x THEN t ELSE t') = IF swapV p x THEN swapC p t ELSE swapC p t'
  swapC p (f $ x) = swapV p f $ swapV p x
  swapC p (PREC x t t' q) = PREC (swapV p x) (swapC p t) (swapC (there (there p)) t') q
  swapC p (LET t IN t') = LET swapC p t IN swapC (there p) t'
  swapC p (CCAST t q) = CCAST (swapC p t) q

{-
lemma-swap-var : {Γ : Ctx} (ρ : ⟪ Γ ⟫X) →
                 {σ : VType} (p : σ ∈ Γ) →
                 {τ : VType} (x : τ ∈ Γ) →
                 proj x ρ ≡ proj (swapvar p x) (swap ρ p)
lemma-swap-var ρ p x = {!!}

mutual
  lemma-swapV : {Γ : Ctx} (ρ : ⟪ Γ ⟫X) →
                {σ : VType} (p : σ ∈ Γ) →
                {τ : VType} (t : VTerm Γ τ) →
                ⟦ t ⟧V ρ ≡ ⟦ swapV p t ⟧V (swap ρ p)
  lemma-swapV ρ p TT = refl
  lemma-swapV ρ p FF = refl
  lemma-swapV ρ p ZZ = refl
  lemma-swapV ρ p (SS t) = cong suc (lemma-swapV ρ p t)
  lemma-swapV ρ p ⟨ t , t' ⟩ = cong₂ _,_ (lemma-swapV ρ p t) (lemma-swapV ρ p t')
  lemma-swapV ρ p (FST t) = cong proj₁ (lemma-swapV ρ p t)
  lemma-swapV ρ p (SND t) = cong proj₂ (lemma-swapV ρ p t)
  lemma-swapV ρ p (VAR x) = lemma-swap-var ρ p x
  lemma-swapV ρ p (LAM σ t) = funext (λ z → ⟦ t ⟧C (z , ρ)) (λ x → ⟦ swapC (there p) {!t!} ⟧C {!!}) (λ x → trans (lemma-swapC (x , ρ) (here' refl) t) {!!})
  lemma-swapV ρ p (VCAST t q) = cong (vcast q) (lemma-swapV ρ p t)
  
  lemma-swapC : {Γ : Ctx} (ρ : ⟪ Γ ⟫X) →
                {σ : VType} (p : σ ∈ Γ) →
                {τ : CType} (t : CTerm Γ τ) →
                ⟦ t ⟧C ρ ≡ ⟦ swapC p t ⟧C (swap ρ p)
  lemma-swapC = {!!}
  
-}
