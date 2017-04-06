{-# OPTIONS --type-in-type #-}

module ESemantics where

open import Data.Unit hiding (_≟_; _≤_)
open import Data.Product

open import Data.Maybe
open import Data.Fin hiding (lift)
open import Data.Nat hiding (_≟_; _⊔_; _≤_)
open import Data.Bool hiding (T ; _≟_; _∨_)
open import Data.List
open import Relation.Binary.Core using (_≡_ ; refl)
open import Relation.Binary.PropositionalEquality

open import Finiteness
open import ELanguage
open import GradedMonad
open import OrderedMonoid
open import Exception
open OrderedMonoid.OrderedMonoid ExcEffOM
open GradedMonad.GradedMonad ExcEffGM


sfail : {X : Set} → T err X
sfail = tt

{-
sor : {e e' : E} {X : Set} → T e X → T e' X → T (e ⊔ e') X 
sor {err} {err} _ _ = tt
sor {err} {ok} _ x' = just x'
sor {err} {errok} _ x' = x'
sor {ok} {err} x _ = just x
sor {ok} {ok} x _ = x
sor {ok} {errok} x _ = just x
sor {errok} (just x) x' = just x
sor {errok} {err} nothing x' = nothing
sor {errok} {ok} nothing x' = just x'
sor {errok} {errok} nothing x' = x'
-}

sor : (e e' : E) {X : Set} → T e X → T e' X → T (e ⊹ e') X
sor err _ _ x' = x'
sor ok _ x _ = x
sor errok err x _ = x
sor errok ok (just x) _ = x
sor errok ok nothing x' = x'
sor errok errok (just x) x' = just x
sor errok errok nothing x' = x'


----------------------------------------------------------------------

mutual
  ⟪_⟫v : VType → Set
  ⟪ nat ⟫v = ℕ
  ⟪ bool ⟫v = Bool
  ⟪ t ∏ u ⟫v = ⟪ t ⟫v × ⟪ u ⟫v
  ⟪ t ⟹ c ⟫v = ⟪ t ⟫v → ⟪ c ⟫c

  ⟪_⟫c : CType → Set
  ⟪ ε / t ⟫c = T ε ⟪ t ⟫v

⟦_⟧x : Ctx → Set
⟦ [] ⟧x = ⊤
⟦ σ ∷ Γ ⟧x = ⟪ σ ⟫v × ⟦ Γ ⟧x


proj : {Γ : Ctx} {σ : VType} → σ ∈ Γ → ⟦ Γ ⟧x → ⟪ σ ⟫v
proj (here' refl) ρ = proj₁ ρ
proj (there x) ρ = proj x (proj₂ ρ)


primrecT : {e e' : E} {t : Set} → ℕ → T e' t → (ℕ → t → T e t) → e' · e ⊑ e' → T e' t
primrecT zero z s p = z
primrecT {e} {e'} (suc n) z s p = sub p (lift {e'} {e} (s n) (primrecT n z s p)) 


mutual
  vcast : {σ σ' : VType} →  σ ≤V σ' → ⟪ σ ⟫v → ⟪ σ' ⟫v
  vcast st-refl x = x
  vcast st-bn x = 0
  --vcast (st-trans o o') x = vcast o' (vcast o x)
  vcast (st-prod o o') (proj , proj') = vcast o proj , vcast o' proj'
  vcast (st-func e o) f = λ x → ccast o (f (vcast e x))

  ccast : {τ τ' : CType} → τ ≤C τ' → ⟪ τ ⟫c → ⟪ τ' ⟫c
  ccast (st-comp {ε} {ε'} e o) c = T₁ {ε'} (vcast o) (sub e c)

mutual
  ⟦_⟧v : {Γ : Ctx} {σ : VType} → VTerm' Γ ( σ) → ⟦ Γ ⟧x → ⟪ σ ⟫v
  ⟦ TT ⟧v ρ = true
  ⟦ FF ⟧v ρ = false
  ⟦ ZZ ⟧v ρ = zero
  ⟦ SS t ⟧v ρ = suc (⟦ t ⟧v ρ)
  ⟦ ⟨ t , t' ⟩ ⟧v ρ = ⟦ t ⟧v ρ , ⟦ t' ⟧v ρ
  ⟦ FST t ⟧v ρ = proj₁ (⟦ t ⟧v ρ)
  ⟦ SND t ⟧v ρ = proj₂ (⟦ t ⟧v ρ)
  ⟦ VAR x ⟧v ρ = proj x ρ
--  ⟦ LAM σ {_ / _} t ⟧v ρ = λ x → ⟦ t ⟧c (x , ρ)
  ⟦ LAM σ t ⟧v ρ = λ x → ⟦ t ⟧c (x , ρ)
  ⟦ VCAST t p ⟧v ρ = vcast p (⟦ t ⟧v ρ)
  
  --⟦_⟧c : {Γ : Ctx} {e : E} {σ : VType} → CTerm Γ (e / σ) → ⟦ Γ ⟧x → T e ⟪ σ ⟫v
  ⟦_⟧c : {Γ : Ctx} {τ : CType} → CTerm' Γ τ → ⟦ Γ ⟧x → ⟪ τ ⟫c
  ⟦ VAL v ⟧c ρ = η (⟦ v ⟧v ρ)
  ⟦ FAIL σ ⟧c ρ = sfail {⟪ σ ⟫v}
  ⟦ TRY_WITH_ {e} {e'} t u ⟧c ρ = sor e e' (⟦ t ⟧c ρ) (⟦ u ⟧c ρ)
  ⟦ IF_THEN_ELSE_ {e} {e'} b m n ⟧c ρ = if ⟦ b ⟧v ρ
                                       then (sub (lub e e') (⟦ m ⟧c ρ))
                                       else (sub (lub-sym e' e) (⟦ n ⟧c ρ))
  --⟦ PREC v m n p ⟧c ρ = primrecT (⟦ v ⟧v ρ) (⟦ m ⟧c ρ) (λ i → λ acc → ⟦ n ⟧c (acc , i , ρ)) p
  ⟦ t $ u ⟧c ρ = ⟦ t ⟧v ρ (⟦ u ⟧v ρ)
  ⟦ LET_IN_ {e} {e'} m n ⟧c ρ = lift {e} {e'} (λ x → ⟦ n ⟧c (x , ρ)) (⟦ m ⟧c ρ)
  ⟦ CCAST t o ⟧c ρ = ccast o (⟦ t ⟧c ρ)


--xxx = ⟦_⟧c ((VAR here) $ ZZ ) (suc , tt)


wk : {Γ : Ctx} → ⟦ Γ ⟧x → {σ : VType} →  ⟪ σ ⟫v → (x : Fin (suc (length Γ))) → 
     ⟦ wkT Γ σ x  ⟧x 
wk ρ v zero =  v , ρ
wk {[]} tt v (suc x) = v , tt
wk {_ ∷ _} (w , ρ) v (suc x) = w , wk ρ v x

lemmaVar : {Γ : Ctx} → (ρ : ⟦ Γ ⟧x) → {σ : VType} 
  →  (v : ⟪ σ ⟫v) → (x : Fin (suc (length Γ))) 
  → {τ : VType} → (y : τ ∈  Γ) → proj (wkvar x y) (wk ρ v x) ≡ proj y ρ
lemmaVar ρ v zero y = refl
lemmaVar ρ v (suc x) (here' refl) = refl
lemmaVar {_ ∷ Γ} (_ , ρ) v (suc x) (there y) = lemmaVar ρ v x y


mutual 
 lemmaV : {Γ : Ctx} → (ρ : ⟦ Γ ⟧x) → {σ : VType} 
  →  (v : ⟪ σ ⟫v) → (x : Fin (suc (length Γ))) 
  → {τ : VType} → (t : VTerm' Γ τ) → ⟦ wkV x t ⟧v (wk ρ v x) ≡ ⟦ t ⟧v ρ
 lemmaV ρ v x TT = refl
 lemmaV ρ v x FF = refl
 lemmaV ρ v x ZZ = refl
 lemmaV ρ v x (SS t) = cong suc (lemmaV ρ v x t)
 lemmaV ρ v x ⟨ t , u ⟩ = {!!}
 lemmaV ρ v x (FST t) =  cong proj₁ (lemmaV ρ v x t)
 lemmaV ρ v x (SND t) = cong proj₂ (lemmaV ρ v x t)
 lemmaV ρ v x (VAR y) = lemmaVar ρ v x y
 lemmaV ρ v x (LAM σ t) =  funext (λ z → ⟦ wkC (suc x) t ⟧c (z , wk ρ v x)) (λ z → ⟦ t ⟧c (z , ρ)) (λ z → lemmaC (z , ρ) v (suc x) t) 
 lemmaV ρ v x (VCAST t p) = {!!}
  
 lemmaC : {Γ : Ctx} → (ρ : ⟦ Γ ⟧x) → {σ : VType} 
  →  (v : ⟪ σ ⟫v) → (x : Fin (suc (length Γ))) 
  → {τ : CType} → (t : CTerm' Γ τ) → ⟦ wkC x t ⟧c (wk ρ v x) ≡ ⟦ t ⟧c ρ
 lemmaC ρ v x t = {!!}

dead-comp' : {Γ : Ctx} {σ τ : VType} {ε : Exc}
             (m : CTerm' Γ (ok / σ)) (n : CTerm' Γ (ε / τ ) ) →
             -- show that n does not depend on m
             (ρ : ⟦ Γ ⟧x) → 
             ⟦ LET m IN (wkC zero n) ⟧c ρ ≡ ⟦ n ⟧c ρ --λ ρ → ⟦ n ⟧c (⟦ m ⟧c ρ , ρ)
dead-comp' m n ρ = lemmaC ρ (⟦ m ⟧c ρ) zero n 

