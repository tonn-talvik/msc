module Optimization where

open import Data.Nat
open import Data.Unit
open import Data.Vec hiding (here)
open import Relation.Binary.PropositionalEquality

open import Finiteness
open import Grading
open import NonDetBoundedVec
open Grading.OrderedMonoid ℕ*
open Grading.GradedMonad NDBV
open import Raw
open import Refined
open import Types
open import Inference
open import Semantics
open import Structural

fail : {X : Set} (m : T 0 X) → m ≡ bv [] z≤n
fail (bv [] z≤n) = refl

{-
-- Incomplete pattern matching ?
dead-comp : {e : E} {X Y : Set} → (m : T 1 X) → (n : T e Y) →
            sub-eq lu (lift {1} {e} (λ _ → n) m) ≡ n
dead-comp (bv [] z≤n) (bv [] z≤n) = {!!}
dead-comp (bv (x ∷ []) (s≤s z≤n)) (bv [] z≤n) = ?
--                  \__ this was given by Agda case-distinction
dead-comp m (bv (x ∷ x₁) x₂) = {!!}
-}

{-
-- should be M : T₁₊X instead of T₁X
dead-comp : {e : E} {X Y : Set} → (m : T 1 X) → (n : T e Y) →
            sub-eq lu (lift {1} {e} (λ _ → n) m) ≡ n
dead-comp (bv [] z≤n) (bv [] z≤n) = subeq-air ru+ []
dead-comp (bv (x ∷ []) (s≤s z≤n)) (bv [] z≤n) = subeq-air ru+ []
dead-comp (bv (x ∷ x' ∷ xs) (s≤s ())) (bv [] z≤n)
dead-comp m (bv (x ∷ x₁) x₂) = {!!}
-}


dup-comp' : {e : E} {X Y : Set} → (m : T 1 X) → (n : X → X → T e Y) → 
            sub-eq lu (bind {1} {1 · e}
                            (λ x → bind {1} {e} (λ y → n y x) m)
                            m)
            ≡ bind {1} {e} (λ x → n x x) m
dup-comp' (bv [] z≤n) f = subeq-air ru+ []
dup-comp' (bv (x ∷ []) (s≤s z≤n)) f with f x x
... | bv ys p = ru++ (ys ++ []) (mon+ p z≤n)








failure : {Γ : Ctx} {X : VType} (m : CTerm Γ (0 / X)) →
          (ρ : ⟪ Γ ⟫X) → 
          ⟦ m ⟧C ρ ≡ ⟦ FAIL X ⟧C ρ
failure m ρ with ⟦ m ⟧C ρ
... | bv [] z≤n = refl


{-
dead-comp : {Γ : Ctx} {σ σ' : VType} {e : ℕ}
            (m : CTerm Γ (1+ / σ)) (n : CTerm Γ (e / σ')) →
            (ρ : ⟪ Γ ⟫X) → 
            sube⟦ LET m IN (wkC ? n) ⟧C ρ ≡ ⟦ n ⟧C ρ
dead-comp m n ρ = ? --lemma-wkC (⟦ m ⟧C ρ , ρ) here n
-}

errok-seq : (e : ℕ) → 1 · (1 · e) ≡ 1 · e
errok-seq e = sym (ass {1} {1} {e})


dup-comp : {e : ℕ} {Γ : Ctx} {X Y : VType} 
           (m : CTerm Γ (1 / X)) (n : CTerm (dupX here) (e / Y)) →
           (ρ : ⟪ Γ ⟫X) → 
           sub-eq (errok-seq e)
                  (⟦ LET m IN LET wkC here m IN n ⟧C ρ)
           ≡ ⟦ LET m IN ctrC here n ⟧C ρ
dup-comp m n ρ with ⟦ m ⟧C ρ
dup-comp {e} m n ρ | bv [] z≤n = subeq-air (sym (trans (+ass {e}) refl)) []
dup-comp m n ρ | bv (x ∷ []) (s≤s z≤n) = {!!}
