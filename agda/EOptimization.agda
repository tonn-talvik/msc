{-# OPTIONS --type-in-type #-}

module EOptimization where

open import Data.Maybe
open import Data.List
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; cong)

open import Exception
open import Finiteness
open import OrderedMonoid
open OrderedMonoid.OrderedMonoid ExcEffOM
open import OLanguage
open import ESemantics

-----------------------------------------------------------

prg0 = FAIL {Γ = []} {σ = nat}
run0 = ⟦ prg0 ⟧ tt

prg1 : CTerm [] (err / nat)
prg1 = IF FF THEN FAIL ELSE FAIL
run1 = ⟦ prg1 ⟧ tt

test = run0 ≡ run1


fail-eq : {Γ : Ctx} {σ : VType} (t : CTerm Γ (err / σ)) → (ρ : ⟦ Γ ⟧x) → ⟦ t ⟧ ρ ≡ ⟦ FAIL {σ = σ} ⟧ ρ
fail-eq t ρ = {!!}
