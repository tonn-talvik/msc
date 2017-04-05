module Optimization where

open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import Exception
open import Grading
open Grading.OrderedMonoid ExcEffOM
open Grading.GradedMonad ExcEffGM
open import Raw
open import Refined
open import Semantics
open import Types

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
              (m₁ : CTerm Γ (e₁ / X)) (m₂ : CTerm Γ (e₂ / X)) (m₃ : CTerm Γ (e₃ / X)) →
              sub-eq (⊹-ass e₁ e₂ e₃) (⟦ TRY m₁ WITH (TRY m₂ WITH m₃) ⟧c ρ) ≡ ⟦ TRY (TRY m₁ WITH m₂) WITH m₃ ⟧c ρ
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

skippy : {e : Exc} {Γ : Ctx} {X Y : VType} →
         CTerm Γ (e / Y) → CTerm (X ∷ Γ) (e / Y)
skippy {e} {Y = Y} m = subst (λ Γ → CTerm Γ (e / Y)) {!sure, trust me!} m

swappy : {e : Exc} {Γ : Ctx} {X Y Z : VType} →
         CTerm (X ∷ Y ∷ Γ) (e / Z) → CTerm (Y ∷ X ∷ Γ) (e / Z)
swappy m = {!!}

-- show m&n independence?
comm : {e₁ e₂ e₃ : Exc} {Γ : Ctx} {ρ : ⟪ Γ ⟫x} {X Y Z : VType}
       (m : CTerm Γ (e₁ / Y)) (n : CTerm Γ (e₂ / X)) →(o : CTerm (X ∷ Y ∷ Γ) (e₃ / Z)) →
       sub-eq (·-comm e₁ e₂)
       (⟦ LET m IN LET skippy n IN o ⟧c ρ) ≡ ⟦ LET n IN LET skippy m IN swappy o ⟧c ρ
comm m n o = {!!}


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

fail : {X : Set} (m : T err X) → m ≡ tt
fail m = refl

failure : {Γ : Ctx} {X : VType} (m : CTerm Γ (err / X)) →
          ⟦ m ⟧c ≡ ⟦ FAIL X ⟧c
failure m = refl


dead-comp : {e : Exc} {X Y : Set} → (m : T ok X) → (n : T e Y) →
            lift {ok} {e} (λ _ → n) m ≡ n
dead-comp m n = refl


{-
need to compare:

lift {errok} {errok · e'}  (λ x → lift {errok} {e'} (λ y → ⟦ n ⟧c (y , x , ρ)) (⟦ m ⟧c ρ)) ((⟦ m ⟧c ρ)

lift {errok} {e'} (λ x → ⟦ n ⟧c (x , x , ρ)) (⟦ m ⟧c ρ)
-}

errok-seq : (e : Exc) → errok · (errok · e) ≡ errok · e
errok-seq e = sym (ass {errok} {errok} {e})


dup-comp : {e : Exc} {X Y : Set} → (m : T errok X) → (n : X → X → T e Y) → 
           sub-eq (errok-seq e) (lift {errok} {errok · e}
                                      (λ x → lift {errok} {e} (λ y → n y x) m)
                                      m)
           ≡ lift {errok} {e} (λ x → n x x) m
dup-comp {err} m n = refl
dup-comp {ok} (just x) n =  refl
dup-comp {ok} nothing n = refl
dup-comp {errok} (just x) n = refl
dup-comp {errok} nothing n = refl 


-- funky context:
--   when term is well-typed in context,
--   it is also well-typed in slightly larger context
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

