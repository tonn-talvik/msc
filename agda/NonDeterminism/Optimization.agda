module Optimization where

open import Data.Nat
open import Data.Unit
open import Data.Vec
open import Relation.Binary.PropositionalEquality

open import Grading
open import NonDetBoundedVec
open Grading.OrderedMonoid ℕ*
open Grading.GradedMonad NDBV
open import Raw
open import Refined
open import Types
open import Inference

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


dup-comp : {e : E} {X Y : Set} → (m : T 1 X) → (n : X → X → T e Y) → 
           sub-eq lu (bind {1} {1 · e}
                           (λ x → bind {1} {e} (λ y → n y x) m)
                           m)
           ≡ bind {1} {e} (λ x → n x x) m
dup-comp (bv [] z≤n) f = subeq-air ru+ []
dup-comp (bv (x ∷ []) (s≤s z≤n)) f with f x x
... | bv ys p = ru++ (ys ++ []) (mon+ p z≤n)


