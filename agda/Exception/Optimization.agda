module Optimization where

open import Data.Bool hiding (T)
open import Data.Fin
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Exception
open import Finiteness
open import Grading
open Grading.OrderedMonoid ExcEffOM
open Grading.GradedMonad ExcEffGM
open import Raw
open import Refined
open import Semantics
open import Types
open import Structural


---------------------------------------------------------------

---------------------------------
-- monad-specific, effect-independent equivalences

-- choice

⊹-itself : (e : Exc) → e ⊹ e ≡ e
⊹-itself err = refl
⊹-itself ok = refl
⊹-itself errok = refl

the-same : {e : Exc} {Γ : Ctx} {ρ : ⟪ Γ ⟫x} {X : VType}
           (m : CTerm Γ (e / X)) →
           sub-eq (⊹-itself e) (⟦ TRY m WITH m ⟧c ρ) ≡ ⟦ m ⟧c ρ
the-same {err} m = refl
the-same {ok} m = refl
the-same {errok} {ρ = ρ} m with ⟦ m ⟧c ρ
... | just _ = refl
... | nothing = refl


⊹-ass : (e e' e'' : Exc) → e ⊹ (e' ⊹ e'') ≡ (e ⊹ e') ⊹ e''
⊹-ass err e' e'' = refl
⊹-ass ok e' e'' = refl
⊹-ass errok err e'' = refl
⊹-ass errok ok e'' = refl
⊹-ass errok errok err = refl
⊹-ass errok errok ok = refl
⊹-ass errok errok errok = refl

handler-ass : {e₁ e₂ e₃ : Exc} {Γ : Ctx} {ρ : ⟪ Γ ⟫x} {X : VType}
              (m₁ : CTerm Γ (e₁ / X)) (m₂ : CTerm Γ (e₂ / X))
              (m₃ : CTerm Γ (e₃ / X)) →
              sub-eq (⊹-ass e₁ e₂ e₃)
                     (⟦ TRY m₁ WITH (TRY m₂ WITH m₃) ⟧c ρ)
              ≡ ⟦ TRY (TRY m₁ WITH m₂) WITH m₃ ⟧c ρ
handler-ass {err} m₁ m₂ m₃ = refl
handler-ass {ok} m₁ m₂ m₃ = refl
handler-ass {errok} {err} m₁ m₂ m₃ = refl
handler-ass {errok} {ok} m₁ m₂ m₃ = refl
handler-ass {errok} {errok} {err} m₁ m₂ m₃ = refl
handler-ass {errok} {errok} {ok} {ρ = ρ} m₁ m₂ m₃ with ⟦ m₁ ⟧c ρ
... | just _ = refl
... | nothing = refl
handler-ass {errok} {errok} {errok} {ρ = ρ} m₁ m₂ m₃ with ⟦ m₁ ⟧c ρ
... | just x = refl
... | nothing = refl


-- commutativity

·-comm : (e e' : Exc) {e'' : Exc} → e · (e' · e'') ≡ e' · (e · e'')
·-comm err err = refl
·-comm err ok = refl
·-comm err errok = refl
·-comm ok err = refl
·-comm ok ok = refl
·-comm ok errok = refl
·-comm errok err = refl
·-comm errok ok = refl
·-comm errok errok = refl

{-
swappy : {e : Exc} {Γ : Ctx} {X Y Z : VType} →
         CTerm (X ∷ Y ∷ Γ) (e / Z) → CTerm (Y ∷ X ∷ Γ) (e / Z)
swappy m = {!!}

-- show m&n independence?
comm : {e₁ e₂ e₃ : Exc} {Γ : Ctx} {ρ : ⟪ Γ ⟫x} {X Y Z : VType}
       (m : CTerm Γ (e₁ / Y)) (n : CTerm Γ (e₂ / X)) (o : CTerm (X ∷ Y ∷ Γ) (e₃ / Z)) →
       sub-eq (·-comm e₁ e₂)
              (⟦ LET m IN LET wkC zero n IN o ⟧c ρ) ≡ ⟦ LET n IN LET wkC zero m IN swappy o ⟧c ρ
comm m n o = {!!}
-}

-- distribution

fails-earlier : {e : Exc} {Γ : Ctx} {ρ : ⟪ Γ ⟫x} {X Y : VType}
                (m : CTerm (X ∷ Γ) (e / Y)) →
                ⟦ LET FAIL X IN m ⟧c ρ ≡ ⟦ FAIL X ⟧c ρ
fails-earlier m = refl


err-anyway : (e : Exc) → e · err ≡ err
err-anyway err = refl
err-anyway ok = refl
err-anyway errok = refl

fails-later : {e : Exc} {Γ : Ctx} {ρ : ⟪ Γ ⟫x} {X Y : VType}
              (m : CTerm Γ (e / X)) →
              sub-eq (err-anyway e) (⟦ LET m IN FAIL Y ⟧c ρ) ≡ ⟦ FAIL Y ⟧c ρ
fails-later m = refl


---------------------------------
--effect-dependent equivalences

failure : {Γ : Ctx} {X : VType} (m : CTerm Γ (err / X)) →
          ⟦ m ⟧c ≡ ⟦ FAIL X ⟧c
failure m = refl


dead-comp : {Γ : Ctx} {σ τ : VType} {ε : Exc}
            (m : CTerm Γ (ok / σ)) (n : CTerm Γ (ε / τ ) ) →
            (ρ : ⟪ Γ ⟫x) → 
            ⟦ LET m IN (wkC zero n) ⟧c ρ ≡ ⟦ n ⟧c ρ
dead-comp m n ρ = lemmaC ρ (⟦ m ⟧c ρ) zero n 


errok-seq : (e : Exc) → errok · (errok · e) ≡ errok · e
errok-seq e = sym (ass {errok} {errok} {e})


dup-comp' : {e : Exc} {Γ : Ctx} {X Y : VType} 
            (m : CTerm Γ (errok / X)) (n : CTerm (ctrT here) (e / Y)) →
            (ρ : ⟪ Γ ⟫x) → 
            sub-eq (errok-seq e)
                   (⟦ LET m IN LET wkC zero m IN n ⟧c ρ)
            ≡ ⟦ LET m IN ctrC here n ⟧c ρ
dup-comp' {err} m n ρ = refl
dup-comp' {ok} m n ρ with ⟦ m ⟧c ρ | inspect ⟦ m ⟧c ρ
dup-comp' {ok} m n ρ | just x | [ eq ] rewrite lemmaC ρ x zero m | eq = cong just (lemma-ctrC (x , ρ) here n)
dup-comp' {ok} m n ρ | nothing | _ = refl
dup-comp' {errok} m n ρ with ⟦ m ⟧c ρ | inspect (⟦ m ⟧c) ρ 
dup-comp' {errok} m n ρ | just x | [ eq ] rewrite lemmaC ρ x zero m | eq = lemma-ctrC (x , ρ) here n
dup-comp' {errok} m n ρ | nothing | _ = refl

