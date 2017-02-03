module Semantics where

open import Data.Unit hiding (_≟_)
open import Data.Product

open import Data.Nat hiding (_≟_)
open import Data.Bool hiding (T ; _≟_)
open import Data.List
open import Data.String hiding (_++_)


open import Finiteness
open import Language
--open import GradedMonad
--open import OrderedMonoid
--open import NonDeterminism

-- T, η, lift are given by GradedMonad parameter
T : Set → Set
T X = List X

η : {X : Set} → X → T X
η x = [ x ]

lift : {X Y : Set} → (X → T Y) → T X → T Y
lift f []  = []
lift f (x ∷ xs) = f x ++ lift f xs

-- what are these?
sfail : {X : Set} → T X
sfail = []

sor : {X : Set} → T X → T X → T X 
sor = _++_

----------------------------------------------------------------------
  
⟦_⟧v : VType → Set
⟦ nat ⟧v = ℕ
⟦ bool ⟧v = Bool
⟦ t ⇒ u ⟧v = ⟦ t ⟧v → T ⟦ u ⟧v
⟦ t ∏ u ⟧v = ⟦ t ⟧v × ⟦ u ⟧v
⟦ err ⟧v = String


⟦_⟧l : Ctx → Set
⟦ [] ⟧l = ⊤
⟦ σ ∷ Γ ⟧l = ⟦ σ ⟧v × ⟦ Γ ⟧l


proj : {Γ : Ctx} → {σ : VType} → σ ∈ Γ → ⟦ Γ ⟧l → ⟦ σ ⟧v
proj (here' p) ρ rewrite p = proj₁ ρ
proj (there x) ρ = proj x (proj₂ ρ)


primrecT : {t : Set} → ℕ → T t → (ℕ → t → T t) → T t
primrecT zero z s = z
primrecT (suc n) z s = lift (s n) (primrecT n z s)


mutual
  ⟦_⟧t : {Γ : Ctx} → {σ : VType} → VTerm Γ σ → ⟦ Γ ⟧l → ⟦ σ ⟧v
  ⟦ TT ⟧t ρ = true
  ⟦ FF ⟧t ρ = false
  ⟦ ZZ ⟧t ρ = zero
  ⟦ SS t ⟧t ρ = suc (⟦ t ⟧t ρ)
  ⟦ ⟨ t , u ⟩ ⟧t ρ = ⟦ t ⟧t ρ , ⟦ u ⟧t ρ
  ⟦ FST p ⟧t ρ = proj₁ (⟦ p ⟧t ρ)
  ⟦ SND p ⟧t ρ = proj₂ (⟦ p ⟧t ρ)
  ⟦ VAR x ⟧t ρ = proj x ρ
  ⟦ LAM σ t ⟧t ρ = λ x → ⟦ t ⟧ (x , ρ)
  ⟦ ERR s ⟧t ρ = s
  
  ⟦_⟧ : {Γ : Ctx} → {σ : VType} → CTerm Γ σ → ⟦ Γ ⟧l → T ⟦ σ ⟧v
  ⟦ VAL v ⟧ ρ = η (⟦ v ⟧t ρ)
  ⟦ FAIL ⟧ ρ = sfail
  ⟦ CHOOSE t u ⟧ ρ = sor (⟦ t ⟧ ρ) (⟦ u ⟧ ρ)
  ⟦ IF b THEN m ELSE n ⟧ ρ = (if ⟦ b ⟧t ρ then ⟦ m ⟧ else ⟦ n ⟧) ρ
  ⟦ PREC v m n ⟧ ρ = primrecT (⟦ v ⟧t ρ) (⟦ m ⟧ ρ) (λ i → λ acc → ⟦ n ⟧ (acc , i , ρ))
  ⟦ t $ u ⟧ ρ = ⟦ t ⟧t ρ (⟦ u ⟧t ρ)

  ⟦ LET m IN n ⟧ ρ = lift (λ x → ⟦ n ⟧ (x , ρ)) (⟦ m ⟧ ρ)


