{-# OPTIONS --type-in-type #-}

module EOptimization where

open import Data.Maybe
open import Data.List
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; cong)

open import Exception
open import Finiteness
open import OrderedMonoid
open OrderedMonoid.OrderedMonoid ExcEffOM
open import OLanguage
open import ESemantics

-----------------------------------------------------------

mutual  
  ⟦_⟧t : vType → Set
  ⟦ nat ⟧t = ℕ
  ⟦ bool ⟧t = Bool
  ⟦ t ∏ u ⟧t = ⟦ t ⟧t × ⟦ u ⟧t
  ⟦ t ⇒ c ⟧t = ⟦ t ⟧t → ⟦ c ⟧c

  ⟦_⟧c : CType → Set
  ⟦ ε / t ⟧c = T ε ⟦ t ⟧t

⟦_⟧x : Ctx → Set
⟦ [] ⟧x = ⊤
⟦ σ ∷ Γ ⟧x = ⟦ σ ⟧t × ⟦ Γ ⟧x


proj : {Γ : Ctx} {σ : VType} → σ ∈ Γ → ⟦ Γ ⟧x → ⟦ σ ⟧t
proj (here' refl) ρ = proj₁ ρ
proj (there x) ρ = proj x (proj₂ ρ)


primrecT : {e e' : E} {t : Set} → ℕ → T e' t → (ℕ → t → T e t) → e' · e ⊑ e' → T e' t
primrecT zero z s p = z
primrecT {e} {e'} (suc n) z s p = sub p (lift {e'} {e} (s n) (primrecT n z s p)) 


mutual
  tcast : {σ σ' : VType} →  σ ≤V σ' → ⟦ σ ⟧t → ⟦ σ' ⟧t
  tcast st-refl x = x
  tcast (st-trans o o') x = tcast o' (tcast o x)
  tcast (st-prod o o') (proj , proj') = tcast o proj , tcast o' proj'
  tcast (st-func e o) f = λ x → ccast o (f (tcast e x))

  ccast : {c c' : CType} → c ⟪ c' → ⟦ c ⟧c → ⟦ c' ⟧c
  ccast (st-comp {ε} {ε'} e o) c = T₁ {ε'} (tcast o) (sub e c)

mutual
  ⟦_⟧v : {Γ : Ctx} → {σ : VType} → VTerm Γ σ → ⟦ Γ ⟧x → ⟦ σ ⟧t
  ⟦ TT ⟧v ρ = true
  ⟦ FF ⟧v ρ = false
  ⟦ ZZ ⟧v ρ = zero
  ⟦ SS t ⟧v ρ = suc (⟦ t ⟧v ρ)
  ⟦ ⟨ t , u ⟩ ⟧v ρ = ⟦ t ⟧v ρ , ⟦ u ⟧v ρ
  ⟦ FST p ⟧v ρ = proj₁ (⟦ p ⟧v ρ)
  ⟦ SND p ⟧v ρ = proj₂ (⟦ p ⟧v ρ)
  ⟦ VAR x ⟧v ρ = proj x ρ
  ⟦ LAM σ t ⟧v ρ = λ x → ⟦ t ⟧ (x , ρ) -- NOTE: LAM constructor must explicitly state t effect and type
  ⟦ VCAST x p ⟧v ρ = tcast p (⟦ x ⟧v ρ)
  
  ⟦_⟧ : {Γ : Ctx} {e : E} {σ : VType} → CTerm Γ (e / σ) → ⟦ Γ ⟧x → T e ⟦ σ ⟧t
  ⟦ VAL v ⟧ ρ = η (⟦ v ⟧v ρ)
  ⟦ FAIL {σ} ⟧ ρ = sfail {⟦ σ ⟧t}
  ⟦ TRY_WITH_ {e} {e'} t u ⟧ ρ = sor {e} {e'} (⟦ t ⟧ ρ) (⟦ u ⟧ ρ)
  ⟦ IF_THEN_ELSE_ {e} {e'} b m n ⟧ ρ = if ⟦ b ⟧v ρ
                                       then (sub (lub e e') (⟦ m ⟧ ρ))
                                       else (sub (lub-sym e' e) (⟦ n ⟧ ρ))
  --⟦ PREC v m n p ⟧ ρ = primrecT (⟦ v ⟧v ρ) (⟦ m ⟧ ρ) (λ i → λ acc → ⟦ n ⟧ (acc , i , ρ)) p
  ⟦ t $ u ⟧ ρ = ⟦ t ⟧v ρ (⟦ u ⟧v ρ)
  ⟦ LET_IN_ {e} {e'} m n ⟧ ρ = lift {e} {e'} (λ x → ⟦ n ⟧ (x , ρ)) (⟦ m ⟧ ρ)
  ⟦ CCAST t o ⟧ ρ = ccast o (⟦ t ⟧ ρ)



-----------------------------------------------------------

-- Δ : (A : Set) → A × A
-- Δ A = {!!}

-----------------------------------------------------------

prg0 = FAIL {Γ = []} {σ = nat}
run0 = ⟦ prg0 ⟧ tt

prg1 : CTerm [] (err / nat)
prg1 = IF FF THEN FAIL ELSE FAIL
run1 = ⟦ prg1 ⟧ tt

test = run0 ≡ run1


fail-eq : {Γ : Ctx} {σ : VType} (t : CTerm Γ (err / σ)) → (ρ : ⟦ Γ ⟧x) → ⟦ t ⟧ ρ ≡ ⟦ FAIL {σ = σ} ⟧ ρ
fail-eq t ρ = {!!}
