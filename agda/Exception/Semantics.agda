module Semantics where

open import Data.Bool hiding (T)
open import Data.List
open import Data.Maybe
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality

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
  ⟪_⟫V : VType → Set
  ⟪ nat ⟫V = ℕ
  ⟪ bool ⟫V = Bool
  ⟪ σ ● σ' ⟫V = ⟪ σ ⟫V × ⟪ σ' ⟫V
  ⟪ σ ⇒ τ ⟫V = ⟪ σ ⟫V → ⟪ τ ⟫C

  ⟪_⟫C : CType → Set
  ⟪ e / σ ⟫C = T e ⟪ σ ⟫V

⟪_⟫X : Ctx → Set
⟪ [] ⟫X = ⊤
⟪ σ ∷ Γ ⟫X = ⟪ σ ⟫V × ⟪ Γ ⟫X


bool2nat : Bool → ℕ
bool2nat false = 0
bool2nat true  = 1

mutual
  vcast : {σ σ' : VType} →  σ ≤V σ' → ⟪ σ ⟫V → ⟪ σ' ⟫V
  vcast st-refl x = x
  vcast st-bn x = bool2nat x
  vcast (st-prod p q) (l , r) = vcast p l , vcast q r
  vcast (st-func p q) f = λ x → ccast q (f (vcast p x))

  ccast : {τ τ' : CType} → τ ≤C τ' → ⟪ τ ⟫C → ⟪ τ' ⟫C
  ccast (st-comp {_} {e'} p q) c = T₁ {e'} (vcast q) (sub p c)



proj : {Γ : Ctx} {σ : VType} → σ ∈ Γ → ⟪ Γ ⟫X → ⟪ σ ⟫V
proj (here' refl) ρ = proj₁ ρ
proj (there x) ρ = proj x (proj₂ ρ)


primrecT : {e e' : E} {X : Set} →
           ℕ → T e X → (ℕ → X → T e' X) → e · e' ⊑ e → T e X
primrecT zero z s p = z
primrecT {e} {e'} (suc n) z s p =
    sub p (bind {e} {e'} (s n) (primrecT n z s p)) 


or-else : (e e' : E) {X : Set} → T e X → T e' X → T (e ⊹ e') X
or-else err _ _ x' = x'
or-else ok _ x _ = x
or-else errok err x _ = x
or-else errok ok (just x) _ = x
or-else errok ok nothing x' = x'
or-else errok errok (just x) x' = just x
or-else errok errok nothing x' = x'

mutual
  ⟦_⟧V : {Γ : Ctx} {σ : VType} → VTerm Γ σ → ⟪ Γ ⟫X → ⟪ σ ⟫V
  ⟦ TT ⟧V ρ = true
  ⟦ FF ⟧V ρ = false
  ⟦ ZZ ⟧V ρ = zero
  ⟦ SS t ⟧V ρ = suc (⟦ t ⟧V ρ)
  ⟦ ⟨ t , t' ⟩ ⟧V ρ = ⟦ t ⟧V ρ , ⟦ t' ⟧V ρ
  ⟦ FST t ⟧V ρ = proj₁ (⟦ t ⟧V ρ)
  ⟦ SND t ⟧V ρ = proj₂ (⟦ t ⟧V ρ)
  ⟦ VAR x ⟧V ρ = proj x ρ
  ⟦ LAM σ t ⟧V ρ = λ x → ⟦ t ⟧C (x , ρ)
  ⟦ VCAST t p ⟧V ρ = vcast p (⟦ t ⟧V ρ)
  

  ⟦_⟧C : {Γ : Ctx} {τ : CType} → CTerm Γ τ → ⟪ Γ ⟫X → ⟪ τ ⟫C
  ⟦ VAL x ⟧C ρ = η (⟦ x ⟧V ρ)
  ⟦ FAIL σ ⟧C ρ = tt
  ⟦ TRY_WITH_ {e} {e'} t t' ⟧C ρ = or-else e e' (⟦ t ⟧C ρ) ( (⟦ t' ⟧C ρ))
  ⟦ IF_THEN_ELSE_ {e} {e'} x t t' ⟧C ρ =
      if ⟦ x ⟧V ρ
      then (sub (lub e e') (⟦ t ⟧C ρ))
      else (sub (lub-sym e' e) (⟦ t' ⟧C ρ))
  ⟦ PREC x t t' p ⟧C ρ = primrecT (⟦ x ⟧V ρ) (⟦ t ⟧C ρ)
                                  ((λ i acc → ⟦ t' ⟧C (acc , i , ρ))) p
  ⟦ f $ x ⟧C ρ = ⟦ f ⟧V ρ (⟦ x ⟧V ρ)
  ⟦ LET_IN_ {e} {e'} t t' ⟧C ρ =
      bind {e} {e'} (λ x → ⟦ t' ⟧C (x , ρ)) (⟦ t ⟧C ρ)
  ⟦ CCAST t p ⟧C ρ = ccast p (⟦ t ⟧C ρ)



