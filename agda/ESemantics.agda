module ESemantics where

open import Data.Unit hiding (_≟_)
open import Data.Product

open import Data.Maybe
open import Data.Nat hiding (_≟_)
open import Data.Bool hiding (T ; _≟_)
open import Data.List
open import Data.String hiding (_++_)


open import Finiteness
open import ELanguage
open import GradedMonad
open import Exception
open GradedMonad.GradedMonad ExcEffGM

{-
T : Set → Set
T X = Maybe X

η : {X : Set} → X → T X
η x = just x

lift : {X Y : Set} → (X → T Y) → T X → T Y
lift f (just x) = f x
lift f nothing  = nothing

sfail : {X : Set} → T X
sfail = nothing

sor : {X : Set} → T X → T X → T X 
sor (just x) _ = just x
sor nothing x' = x'
-}

sfail : {X : Set} → T err X
sfail = tt

sor : {ε : E} {X : Set} → T ε X → T ε X → T ε X 
sor {err} x x' = x'
sor {ok} x _ = x
sor {errok} (just x) x' = just x
sor {errok} nothing x' = x'


----------------------------------------------------------------------
  
⟦_⟧t : VType → Set
⟦ nat ⟧t = ℕ
⟦ bool ⟧t = Bool
⟦ t ⇒ ε / u ⟧t = ⟦ t ⟧t → T ε ⟦ u ⟧t
⟦ t ∏ u ⟧t = ⟦ t ⟧t × ⟦ u ⟧t


⟦_⟧c : Ctx → Set
⟦ [] ⟧c = ⊤
⟦ σ ∷ Γ ⟧c = ⟦ σ ⟧t × ⟦ Γ ⟧c


proj : {Γ : Ctx} → {σ : VType} → σ ∈ Γ → ⟦ Γ ⟧c → ⟦ σ ⟧t
proj (here' p) ρ rewrite p = proj₁ ρ
proj (there x) ρ = proj x (proj₂ ρ)


primrecT : {t : Set} → ℕ → T ok t → (ℕ → t → T ok t) → T ok t
primrecT zero z s = z
primrecT (suc n) z s = lift {ok} {ok} (s n) (primrecT n z s)


mutual
  ⟦_⟧v : {Γ : Ctx} → {σ : VType} → VTerm Γ σ → ⟦ Γ ⟧c → ⟦ σ ⟧t
  ⟦ TT ⟧v ρ = true
  ⟦ FF ⟧v ρ = false
  ⟦ ZZ ⟧v ρ = zero
  ⟦ SS t ⟧v ρ = suc (⟦ t ⟧v ρ)
  ⟦ ⟨ t , u ⟩ ⟧v ρ = ⟦ t ⟧v ρ , ⟦ u ⟧v ρ
  ⟦ FST p ⟧v ρ = proj₁ (⟦ p ⟧v ρ)
  ⟦ SND p ⟧v ρ = proj₂ (⟦ p ⟧v ρ)
  ⟦ VAR x ⟧v ρ = proj x ρ
  ⟦ LAM σ t ⟧v ρ = λ x → ⟦ t ⟧ (x , ρ)
  
  ⟦_⟧ : {Γ : Ctx} {ε : E} {σ : VType} → CTerm Γ ε σ → ⟦ Γ ⟧c → T ε ⟦ σ ⟧t
  ⟦ VAL v ⟧ ρ = η (⟦ v ⟧v ρ)
  ⟦ FAIL {σ} ⟧ ρ = sfail {⟦ σ ⟧t}

  ⟦ TRY_WITH_ {ε} t u ⟧ ρ = sor {ε} (⟦ t ⟧ ρ) (⟦ u ⟧ ρ)  
  ⟦ IF b THEN m ELSE n ⟧ ρ = (if ⟦ b ⟧v ρ then ⟦ m ⟧ else ⟦ n ⟧) ρ
  ⟦ PREC v m n ⟧ ρ = primrecT (⟦ v ⟧v ρ) (⟦ m ⟧ ρ) (λ i → λ acc → ⟦ n ⟧ (acc , i , ρ))
  ⟦ t $ u ⟧ ρ = ⟦ t ⟧v ρ (⟦ u ⟧v ρ)

  -- ⟦ LET m IN n ⟧ ρ = lift (λ x → ⟦ n ⟧ (x , ρ)) (⟦ m ⟧ ρ)
  ⟦ LET_IN_ {ε} {ε'} m n ⟧ ρ = lift {ε} {ε'} (λ x → ⟦ n ⟧ (x , ρ)) (⟦ m ⟧ ρ)


