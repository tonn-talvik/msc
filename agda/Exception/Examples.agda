{-# OPTIONS --type-in-type #-}
module Examples where

open import Data.Bool hiding (T)
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Relation.Binary.Core

open import Raw
open import Types
open import Refined
open import Inference
open import Semantics

open import Exception
open import Grading
open Grading.GradedMonad ExcEffGM
open Grading.OrderedMonoid ExcEffOM

open import Optimization

raw1 raw2 raw3 : cTerm
raw1 = IF FF THEN VAL ZZ ELSE (FAIL nat)
raw2 = IF (VAR 0) THEN (FAIL nat) ELSE (FAIL nat)
raw3 = LET VAL ZZ IN VAL (SS ZZ)

inf1 : infer-ctermType [] raw1
inf1 = infer-cterm [] raw1
inf2 = infer-cterm [ bool ] raw2
inf3 = infer-cterm [] raw3

sem1 = ⟦ inf1 ⟧c tt
sem2 = ⟦ inf2 ⟧c (true , tt)
sem3 = ⟦ inf3 ⟧c tt

ss = ⟦ VAL (SS ZZ) ⟧c tt

p : sem3 ≡ ss
p = refl

pp : ⟦ inf3 ⟧c ≡ ⟦ VAL (SS ZZ) ⟧c
pp = refl

⟦_⟧ : (t : cTerm) (Γ : Ctx) {τ : CType} → {p : infer-ctype Γ t ≡ just τ} → ⟪ Γ ⟫x  → ⟪ τ ⟫c
⟦_⟧ t Γ {p = p} with infer-ctype Γ t | infer-cterm Γ t
⟦_⟧ t Γ {p = refl} | just τ | t' = ⟦ t' ⟧c
⟦_⟧ t Γ {p = ()} | nothing | t'


--xxx : {e : Exc} → T e ℕ
--xxx = ⟦ raw3 ⟧ [] tt


fail' : {Γ : Ctx} {X : VType} (m : CTerm Γ (err / X)) → ⟦ m ⟧c ≡ ⟦ FAIL X ⟧c
fail' m = refl


{-
dead-comp' : {Γ : Ctx} {X Y : VType} {e : Exc}
             (m : CTerm Γ (ok / X)) (n : CTerm (X ∷ Γ) (e / Y)) →
             -- show that n does not depend on m
             ⟦ LET m IN n ⟧c ≡ ⟦ {!n!} ⟧c --λ ρ → ⟦ n ⟧c (⟦ m ⟧c ρ , ρ)
dead-comp' m n = {!!}
-}

{-
dup-comp' : {Γ : Ctx} {X Y : VType} {e : Exc}
            (m : CTerm Γ (errok / X)) (n : CTerm (X ∷ X ∷ Γ) (e / Y)) →
            ⟦ LET m IN LET m IN n ⟧c ≡ ⟦ LET m IN n x/y ⟧c
dup-comp' = ?
-}

dup-comp2 : {e : Exc} {Γ : Ctx} {ρ : ⟪ Γ ⟫x} {X Y : VType}
            (m : CTerm Γ (errok / X)) (n : CTerm (X ∷ X ∷ Γ) (e / Y)) → 
            sub-eq (errok-seq e)
                   (lift {errok} {errok · e}
                         (λ x → lift {errok} {e}
                                      (λ y → ⟦ n ⟧c (y , x , ρ))
                                      (⟦ m ⟧c ρ))
                         (⟦ m ⟧c ρ))
            ≡ lift {errok} {e} (λ x → ⟦ n ⟧c (x , x , ρ)) (⟦ m ⟧c ρ)
dup-comp2 {err} m n = refl
--dup-comp2 {ok} m n = {!!} -- Auto ↝ "An internal error has occurred. Please report this as a bug. ..."
dup-comp2 {ok} {ρ = ρ} m n with ⟦ m ⟧c ρ
... | just x = refl
... | nothing = refl
dup-comp2 {errok} {ρ = ρ} m n with ⟦ m ⟧c ρ
... | just x = refl
... | nothing = refl
