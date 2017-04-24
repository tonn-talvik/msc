module Optimization where

open import Data.Nat
open import Data.Product
open import Data.Unit
open import Data.Vec hiding (here)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

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


lemma2 : {m n : ℕ} (p : m ≡ n) →
         sym (trans (cong suc p) refl) ≡ cong suc (sym (trans p refl))
lemma2 refl = refl

lemma : (n : ℕ) → sym (trans (+ass {n} {0} {0}) refl) ≡ ru+
lemma zero = refl
lemma (suc n) =
  begin
    sym (trans (cong suc (+ass {n} {0} {0})) refl)
  ≡⟨ lemma2 (+ass {n}) ⟩ 
    cong suc (sym (trans (+ass {n} {0} {0}) refl))
  ≡⟨ cong (cong suc) (lemma n) ⟩ 
    cong suc ru+
  ∎
something : {X : Set} {n : ℕ} (xs : BVec X n) → 
            sub-eq (sym (trans (+ass {n} {0} {0}) refl))
                  ((xs ++bv (bv [] z≤n)) ++bv (bv [] z≤n))
            ≡ xs ++bv (bv [] z≤n)
something {n = n} (bv xs p) =
  begin
    sub-eq (sym (trans (+ass {n}) refl))
      (bv ((xs ++ []) ++ []) (mon+ (mon+ p z≤n) z≤n))
  ≡⟨ cong (λ q → sub-eq q (bv ((xs ++ []) ++ [])
                               (mon+ (mon+ p z≤n) z≤n)))
          (lemma n) ⟩
    sub-eq ru+ (bv ((xs ++ []) ++ []) (mon+ (mon+ p z≤n) z≤n))
  ≡⟨ ru++ (xs ++ []) (mon+ p z≤n) ⟩
    bv (xs ++ []) (mon+ p z≤n)
  ∎

dup-comp : {e : ℕ} {Γ : Ctx} {X Y : VType} 
           (m : CTerm Γ (1 / X)) (n : CTerm (dupX here) (e / Y)) →
           (ρ : ⟪ Γ ⟫X) → 
           sub-eq (errok-seq e)
                  (⟦ LET m IN LET wkC here m IN n ⟧C ρ)
           ≡ ⟦ LET m IN ctrC here n ⟧C ρ
dup-comp m n ρ with ⟦ m ⟧C ρ | inspect ⟦ m ⟧C ρ
dup-comp {e} m n ρ | bv [] z≤n | _ = subeq-air (sym (trans (+ass {e}) refl)) []
dup-comp m n ρ | bv (x ∷ []) (s≤s z≤n) | [ p ] rewrite lemma-wkC (x , ρ) here m | p | lemma-ctrC (x , ρ) here n = something (⟦ ctrC (here' refl) n ⟧C (x , ρ))
