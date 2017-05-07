module Optimization where

open import Data.Bool hiding (T)
open import Data.Fin
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product hiding (swap)
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
-- monad-specific, effect-independent equivalences

-- choice

⊹-itself : (e : Exc) → e ⊹ e ≡ e
⊹-itself err = refl
⊹-itself ok = refl
⊹-itself errok = refl

the-same : {e : Exc} {Γ : Ctx} {ρ : ⟪ Γ ⟫X} {σ : VType}
           (m : CTerm Γ (e / σ)) →
           sub-eq (⊹-itself e) (⟦ TRY m WITH m ⟧C ρ) ≡ ⟦ m ⟧C ρ
the-same {err} m = refl
the-same {ok} m = refl
the-same {errok} {ρ = ρ} m with ⟦ m ⟧C ρ
... | just _ = refl
... | nothing = refl


⊹-err : (e : Exc) → e ⊹ err ≡ e
⊹-err err = refl
⊹-err ok = refl
⊹-err errok = refl

handler-fails : {e : Exc} {Γ : Ctx} {ρ : ⟪ Γ ⟫X} {σ : VType}
               (m : CTerm Γ (e / σ)) →
               sub-eq (⊹-err e) (⟦ TRY m WITH FAIL σ ⟧C ρ) ≡ ⟦ m ⟧C ρ
handler-fails {err} m = refl
handler-fails {ok} m = refl
handler-fails {errok} m = refl


⊹-ass : (e e' e'' : Exc) → e ⊹ (e' ⊹ e'') ≡ (e ⊹ e') ⊹ e''
⊹-ass err e' e'' = refl
⊹-ass ok e' e'' = refl
⊹-ass errok err e'' = refl
⊹-ass errok ok e'' = refl
⊹-ass errok errok err = refl
⊹-ass errok errok ok = refl
⊹-ass errok errok errok = refl

handler-ass : {e₁ e₂ e₃ : Exc} {Γ : Ctx} {ρ : ⟪ Γ ⟫X} {σ : VType}
              (m₁ : CTerm Γ (e₁ / σ)) (m₂ : CTerm Γ (e₂ / σ))
              (m₃ : CTerm Γ (e₃ / σ)) →
              sub-eq (⊹-ass e₁ e₂ e₃)
                     (⟦ TRY m₁ WITH (TRY m₂ WITH m₃) ⟧C ρ)
              ≡ ⟦ TRY (TRY m₁ WITH m₂) WITH m₃ ⟧C ρ
handler-ass {err} m₁ m₂ m₃ = refl
handler-ass {ok} m₁ m₂ m₃ = refl
handler-ass {errok} {err} m₁ m₂ m₃ = refl
handler-ass {errok} {ok} m₁ m₂ m₃ = refl
handler-ass {errok} {errok} {err} m₁ m₂ m₃ = refl
handler-ass {errok} {errok} {ok} {ρ = ρ} m₁ m₂ m₃ with ⟦ m₁ ⟧C ρ
... | just _ = refl
... | nothing = refl
handler-ass {errok} {errok} {errok} {ρ = ρ} m₁ m₂ m₃ with ⟦ m₁ ⟧C ρ
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
comm : {e₁ e₂ e₃ : Exc} {Γ : Ctx} {X Y Z : VType}
       (m : CTerm Γ (e₁ / Y)) (n : CTerm Γ (e₂ / X)) (o : CTerm (X ∷ Y ∷ Γ) (e₃ / Z)) →
       (ρ : ⟪ Γ ⟫X) →
       sub-eq (·-comm e₁ e₂)
              (⟦ LET m IN LET wkC here n IN o ⟧C ρ)
       ≡ ⟦ LET n IN LET wkC here m IN swapC here o ⟧C ρ
comm {err} {err} m n o ρ = refl
comm {err} {ok} m n o ρ = refl
comm {err} {errok} m n o ρ = refl
comm {ok} {err} m n o ρ = refl
comm {ok} {ok} m n o ρ with ⟦ m ⟧C ρ | ⟦ n ⟧C ρ | inspect ⟦ m ⟧C ρ | inspect ⟦ n ⟧C ρ
... | mm | nn | [ p ] | [ q ] rewrite lemma-wkC (nn , ρ) (here' refl) m | lemma-wkC (mm , ρ) (here' refl) n | p | q = lemma-swapC (nn , mm , ρ) (here' refl) o
comm {ok} {errok} m n o ρ with ⟦ m ⟧C ρ | ⟦ n ⟧C ρ 
... | mm | just nn rewrite lemma-wkC (mm , ρ) (here' refl) m = {!!}
... | mm | nothing = {!!}
comm {errok} {err} m n o ρ = refl
comm {errok} {ok} m n o ρ = {!!}
comm {errok} {errok} m n o ρ = {!!}
-}

-- distribution

fails-earlier : {e : Exc} {Γ : Ctx} {ρ : ⟪ Γ ⟫X} {σ σ' : VType}
                (m : CTerm (σ ∷ Γ) (e / σ')) →
                ⟦ LET FAIL σ IN m ⟧C ρ ≡ ⟦ FAIL σ' ⟧C ρ
fails-earlier m = refl


err-anyway : (e : Exc) → e · err ≡ err
err-anyway err = refl
err-anyway ok = refl
err-anyway errok = refl

fails-later : {e : Exc} {Γ : Ctx} {ρ : ⟪ Γ ⟫X} {σ σ' : VType}
              (m : CTerm Γ (e / σ)) →
              sub-eq (err-anyway e) (⟦ LET m IN FAIL σ' ⟧C ρ) ≡ ⟦ FAIL σ ⟧C ρ
fails-later m = refl



---------------------------------------------------------------
--effect-dependent equivalences

failure : {Γ : Ctx} {σ : VType} (m : CTerm Γ (err / σ)) →
          ⟦ m ⟧C ≡ ⟦ FAIL σ ⟧C
failure m = refl


both-fail : {Γ : Ctx} {σ : VType}
            (m : VTerm Γ bool) (n n' : CTerm Γ (err / σ)) →
            (ρ : ⟪ Γ ⟫X) → 
            ⟦ IF m THEN n ELSE n' ⟧C ρ ≡ ⟦ FAIL σ ⟧C ρ
both-fail m n n' ρ = refl


dead-comp : {Γ : Ctx} {σ σ' : VType} {e : Exc}
            (m : CTerm Γ (ok / σ)) (n : CTerm Γ (e / σ')) →
            (ρ : ⟪ Γ ⟫X) → 
            ⟦ LET m IN (wkC here n) ⟧C ρ ≡ ⟦ n ⟧C ρ
dead-comp m n ρ = lemma-wkC (⟦ m ⟧C ρ , ρ) here n


errok-seq : (e : Exc) → errok · (errok · e) ≡ errok · e
errok-seq e = sym (ass {errok} {errok} {e})

dup-comp : {e : Exc} {Γ : Ctx} {σ σ' : VType} 
           (m : CTerm Γ (errok / σ)) (n : CTerm (dupX here) (e / σ')) →
           (ρ : ⟪ Γ ⟫X) → 
           sub-eq (errok-seq e)
                  (⟦ LET m IN LET wkC here m IN n ⟧C ρ)
           ≡ ⟦ LET m IN ctrC here n ⟧C ρ
dup-comp {err} m n ρ = refl
dup-comp {ok} m n ρ with ⟦ m ⟧C ρ | inspect ⟦ m ⟧C ρ
... | just x  | [ eq ] rewrite lemma-wkC (x , ρ) here m | eq
                  = cong just (lemma-ctrC (x , ρ) here n)
... | nothing | _ = refl
dup-comp {errok} m n ρ with ⟦ m ⟧C ρ | inspect (⟦ m ⟧C) ρ 
... | just x  | [ eq ] rewrite lemma-wkC (x , ρ) here m | eq
                  = lemma-ctrC (x , ρ) here n
... | nothing | _ = refl

