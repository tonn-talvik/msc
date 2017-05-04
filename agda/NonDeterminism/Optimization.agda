module Optimization where

open import Data.List renaming (_∷_ to _∷l_) hiding (_++_)
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

------------------------------------------------------------------
-- monad-specific, effect-independent equivalences

-- choice 1, 2: works on sets, not on vecs

-- choice 3
fail-or-m : {Γ : Ctx} {σ : VType} {e : ℕ} (m : CTerm Γ (e / σ)) →
            (ρ : ⟪ Γ ⟫X) → 
            ⟦ CHOOSE (FAIL σ) m ⟧C ρ ≡ ⟦ m ⟧C ρ
fail-or-m m ρ with ⟦ m ⟧C ρ
... | bv xs p = refl

-- choice 4
choose-ass : {e₁ e₂ e₃ : ℕ} {Γ : Ctx} {σ : VType}
             (m₁ : CTerm Γ (e₁ / σ)) (m₂ : CTerm Γ (e₂ / σ))
             (m₃ : CTerm Γ (e₃ / σ)) (ρ : ⟪ Γ ⟫X) →
             sub-eq (+ass {e₁} {e₂} {e₃})
                    (⟦ CHOOSE m₁ (CHOOSE m₂ m₃) ⟧C ρ)
             ≡ ⟦ CHOOSE (CHOOSE m₁ m₂) m₃ ⟧C ρ
choose-ass m₁ m₂ m₃ ρ with ⟦ m₁ ⟧C ρ | ⟦ m₂ ⟧C ρ | ⟦ m₃ ⟧C ρ
... | bv₁ | bv₂ | bv₃ = lemma-ass++ bv₁ bv₂ bv₃

-- commutativity?

-- distribution?

fails-earlier : {e : ℕ} {Γ : Ctx} {ρ : ⟪ Γ ⟫X} {σ σ' : VType}
                (m : CTerm (σ ∷l Γ) (e / σ')) →
                ⟦ LET FAIL σ IN m ⟧C ρ ≡ ⟦ FAIL σ' ⟧C ρ
fails-earlier m = refl

err-anyway : (n : ℕ) → n · 0 ≡ 0
err-anyway zero = refl
err-anyway (suc n) = err-anyway n

fails-later : {e : ℕ} {Γ : Ctx} {σ σ' : VType}
              (m : CTerm Γ (e / σ)) (ρ : ⟪ Γ ⟫X) →
              sub-eq (err-anyway e) (⟦ LET m IN FAIL σ' ⟧C ρ) ≡ ⟦ FAIL σ' ⟧C ρ
fails-later m ρ with ⟦ m ⟧C ρ
fails-later m ρ | bv [] p = {!!}
fails-later m ρ | bv (x ∷ xs) p = {!!}

------------------------------------------------------------------
-- effect-dependent equivalences


failure : {Γ : Ctx} {σ : VType} (m : CTerm Γ (0 / σ)) →
          (ρ : ⟪ Γ ⟫X) → 
          ⟦ m ⟧C ρ ≡ ⟦ FAIL σ ⟧C ρ
failure m ρ with ⟦ m ⟧C ρ
... | bv [] z≤n = refl


{-
-- requires ND1+
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

dup-comp : {e : ℕ} {Γ : Ctx} {σ σ' : VType} 
           (m : CTerm Γ (1 / σ)) (n : CTerm (dupX here) (e / σ')) →
           (ρ : ⟪ Γ ⟫X) → 
           sub-eq (errok-seq e)
                  (⟦ LET m IN LET wkC here m IN n ⟧C ρ)
           ≡ ⟦ LET m IN ctrC here n ⟧C ρ
dup-comp m n ρ with ⟦ m ⟧C ρ | inspect ⟦ m ⟧C ρ
dup-comp {e} m n ρ | bv [] z≤n | _ = subeq-air (sym (trans (+ass {e}) refl)) []
dup-comp m n ρ | bv (x ∷ []) (s≤s z≤n) | [ p ] rewrite lemma-wkC (x , ρ) here m | p | lemma-ctrC (x , ρ) here n = something (⟦ ctrC (here' refl) n ⟧C (x , ρ))


{-
pure lambda hoist requires ND1
-}
