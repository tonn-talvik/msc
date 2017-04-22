module Sugar where

open import Data.Fin hiding (_<_)
open import Data.Nat
open import Data.List
open import Relation.Nullary

open import Raw
open import Refined
open import Types
open import Finiteness


lemma-<? : (Γ : Ctx) (τ : VType) (n : ℕ) →
           ¬ n < length Γ →
           ¬ suc n < length (τ ∷ Γ)
lemma-<? _ _ n p (s≤s q) = p q

_<?_ : (n : ℕ) (Γ : Ctx) → Dec (n < length Γ)
n <? [] = no (λ ())
zero <? (x ∷ Γ) = yes (s≤s z≤n)
suc n <? (x ∷ Γ) with n <? Γ
suc n <? (x ∷ Γ) | yes p = yes (s≤s p)
suc n <? (x ∷ Γ) | no ¬p = no (lemma-<? Γ x n ¬p)


varify :  {Γ : Ctx} (n : ℕ) {p : truncate (n <? Γ)} →
         VTerm Γ (lkp Γ (fromℕ≤ (extract (n <? Γ) {p})))
varify {Γ} n {p} = VAR (trace Γ (fromℕ≤ (extract (n <? Γ) {p})))


natify : ∀ {Γ} → ℕ → VTerm Γ nat
natify zero = ZZ
natify (suc n) = SS (natify n)
