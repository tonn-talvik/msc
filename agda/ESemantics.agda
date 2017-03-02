module ESemantics where

open import Data.Unit hiding (_≟_; _≤_)
open import Data.Product

open import Data.Maybe
open import Data.Nat hiding (_≟_; _⊔_; _≤_)
open import Data.Bool hiding (T ; _≟_; _∨_)
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

sor : {ε ε' : E} {X : Set} → T ε X → T ε' X → T (ε ⊔ ε') X 
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



----------------------------------------------------------------------
  
⟦_⟧t : VType → Set
⟦ nat ⟧t = ℕ
⟦ bool ⟧t = Bool
⟦ t ∏ u ⟧t = ⟦ t ⟧t × ⟦ u ⟧t
⟦ t ⇒ ε / u ⟧t = ⟦ t ⟧t → T ε ⟦ u ⟧t



⟦_⟧c : Ctx → Set
⟦ [] ⟧c = ⊤
⟦ σ ∷ Γ ⟧c = ⟦ σ ⟧t × ⟦ Γ ⟧c


proj : {Γ : Ctx} → {σ : VType} → σ ∈ Γ → ⟦ Γ ⟧c → ⟦ σ ⟧t
proj (here' p) ρ rewrite p = proj₁ ρ
proj (there x) ρ = proj x (proj₂ ρ)


primrecT : {t : Set} → ℕ → T ok t → (ℕ → t → T ok t) → T ok t
primrecT zero z s = z
primrecT (suc n) z s = lift {ok} {ok} (s n) (primrecT n z s)


tcast : {σ σ' : VType} →  σ ≤ σ' → ⟦ σ ⟧t → ⟦ σ' ⟧t
tcast st-refl x = x
tcast (st-trans o o') x = tcast o' (tcast o x)
tcast (st-prod o o') (proj , proj') = tcast o proj , tcast o' proj'
tcast (st-func e o (st-comp e' o')) x = {!!}

ccast : {ε ε' : E} {σ σ' : VType} → ε / σ ⟪ ε' / σ' → T ε ⟦ σ ⟧t → T ε' ⟦ σ' ⟧t
ccast (st-comp e o) c = {!!}

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
  ⟦ VCAST x o ⟧v ρ = tcast o (⟦ x ⟧v ρ)
  
  ⟦_⟧ : {Γ : Ctx} {ε : E} {σ : VType} → CTerm Γ (ε / σ) → ⟦ Γ ⟧c → T ε ⟦ σ ⟧t
  ⟦ VAL v ⟧ ρ = η (⟦ v ⟧v ρ)
  ⟦ FAIL {σ} ⟧ ρ = sfail {⟦ σ ⟧t}
  ⟦ TRY_WITH_ {ε} {ε'} t u ⟧ ρ = sor {ε} {ε'} (⟦ t ⟧ ρ) (⟦ u ⟧ ρ)
  ⟦ IF_THEN_ELSE_ {ε} {ε'} b m n ⟧ ρ = if ⟦ b ⟧v ρ
                                       then (sub (lub ε ε') (⟦ m ⟧ ρ))
                                       else (sub (lub-sym ε' ε) (⟦ n ⟧ ρ))
  ⟦ PREC v m n ⟧ ρ = primrecT (⟦ v ⟧v ρ) (⟦ m ⟧ ρ) (λ i → λ acc → ⟦ n ⟧ (acc , i , ρ))
  ⟦ t $ u ⟧ ρ = ⟦ t ⟧v ρ (⟦ u ⟧v ρ)
  ⟦ LET_IN_ {ε} {ε'} m n ⟧ ρ = lift {ε} {ε'} (λ x → ⟦ n ⟧ (x , ρ)) (⟦ m ⟧ ρ)
  ⟦ CCAST t o ⟧ ρ = ccast o (⟦ t ⟧ ρ)

