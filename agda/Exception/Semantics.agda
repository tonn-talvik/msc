module Semantics where

open import Data.Bool hiding (T)
open import Data.List
open import Data.Maybe
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Unit
open import Relation.Binary.Core

open import Finiteness
open import Grading
open import Exception
open Grading.OrderedMonoid ExcEffOM
open Grading.GradedMonad ExcEffGM
open import Raw
open import Types
open import Refined
open import Inference


----------------------------------------------------------------------

mutual
  ⟪_⟫v : VType → Set
  ⟪ nat ⟫v = ℕ
  ⟪ bool ⟫v = Bool
  ⟪ t ∏ u ⟫v = ⟪ t ⟫v × ⟪ u ⟫v
  ⟪ t ⟹ c ⟫v = ⟪ t ⟫v → ⟪ c ⟫c

  ⟪_⟫c : CType → Set
  ⟪ ε / t ⟫c = T ε ⟪ t ⟫v

⟪_⟫x : Ctx → Set
⟪ [] ⟫x = ⊤
⟪ σ ∷ Γ ⟫x = ⟪ σ ⟫v × ⟪ Γ ⟫x


bool2nat : Bool → ℕ
bool2nat false = 0
bool2nat true  = 1

mutual
  vcast : {σ σ' : VType} →  σ ≤V σ' → ⟪ σ ⟫v → ⟪ σ' ⟫v
  vcast st-refl x = x
  vcast st-bn x = bool2nat x
  vcast (st-prod p q) (l , r) = vcast p l , vcast q r
  vcast (st-func p q) f = λ x → ccast q (f (vcast p x))

  ccast : {τ τ' : CType} → τ ≤C τ' → ⟪ τ ⟫c → ⟪ τ' ⟫c
  ccast (st-comp {_} {e'} p q) c = T₁ {e'} (vcast q) (sub p c)



proj : {Γ : Ctx} {σ : VType} → σ ∈ Γ → ⟪ Γ ⟫x → ⟪ σ ⟫v
proj (here' refl) ρ = proj₁ ρ
proj (there x) ρ = proj x (proj₂ ρ)


primrecT : {e e' : E} {X : Set} → ℕ → T e X → (ℕ → X → T e' X) → e · e' ⊑ e → T e X
primrecT zero z s p = z
primrecT {e} {e'} (suc n) z s p = sub p (lift {e} {e'} (s n) (primrecT n z s p)) 


sfail : {X : Set} → T err X
sfail = tt

sor : (e e' : E) {X : Set} → T e X → T e' X → T (e ⊹ e') X
sor err _ _ x' = x'
sor ok _ x _ = x
sor errok err x _ = x
sor errok ok (just x) _ = x
sor errok ok nothing x' = x'
sor errok errok (just x) x' = just x
sor errok errok nothing x' = x'

mutual
  ⟦_⟧v : {Γ : Ctx} {σ : VType} → VTerm Γ σ → ⟪ Γ ⟫x → ⟪ σ ⟫v
  ⟦ TT ⟧v ρ = true
  ⟦ FF ⟧v ρ = false
  ⟦ ZZ ⟧v ρ = zero
  ⟦ SS t ⟧v ρ = suc (⟦ t ⟧v ρ)
  ⟦ ⟨ t , t' ⟩ ⟧v ρ = ⟦ t ⟧v ρ , ⟦ t' ⟧v ρ
  ⟦ FST t ⟧v ρ = proj₁ (⟦ t ⟧v ρ)
  ⟦ SND t ⟧v ρ = proj₂ (⟦ t ⟧v ρ)
  ⟦ VAR x ⟧v ρ = proj x ρ
  ⟦ LAM σ t ⟧v ρ = λ x → ⟦ t ⟧c (x , ρ)
  ⟦ VCAST t p ⟧v ρ = vcast p (⟦ t ⟧v ρ)
  

  ⟦_⟧c : {Γ : Ctx} {τ : CType} → CTerm Γ τ → ⟪ Γ ⟫x → ⟪ τ ⟫c
  ⟦ VAL x ⟧c ρ = η (⟦ x ⟧v ρ)
  ⟦ FAIL σ ⟧c ρ = sfail {⟪ σ ⟫v}
  ⟦ TRY_WITH_ {e} {e'} t t' ⟧c ρ = sor e e' (⟦ t ⟧c ρ) ( (⟦ t' ⟧c ρ))
  ⟦ IF_THEN_ELSE_ {e} {e'} x t t' ⟧c ρ = if ⟦ x ⟧v ρ
                                         then (sub (lub e e') (⟦ t ⟧c ρ))
                                         else (sub (lub-sym e' e) (⟦ t' ⟧c ρ))
  ⟦ PREC x t t' p ⟧c ρ = primrecT (⟦ x ⟧v ρ)
                                  (⟦ t ⟧c ρ)
                                  ((λ i → λ acc → ⟦ t' ⟧c (acc , i , ρ))) p
  ⟦ t $ u ⟧c ρ = ⟦ t ⟧v ρ (⟦ u ⟧v ρ)
  ⟦ LET_IN_ {e} {e'} m n ⟧c ρ = lift {e} {e'} (λ x → ⟦ n ⟧c (x , ρ)) (⟦ m ⟧c ρ)
  ⟦ CCAST t o ⟧c ρ = ccast o (⟦ t ⟧c ρ)



