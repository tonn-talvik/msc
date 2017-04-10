module Optimization where

open import Data.Bool hiding (T)
open import Data.Fin hiding (lift)
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


wkT : (Γ : Ctx) → (σ : VType) → Fin (suc (length Γ)) → Ctx
wkT Γ σ zero = σ ∷ Γ
wkT [] σ (suc x) = σ ∷ []
wkT (σ' ∷ Γ) σ (suc x) = σ' ∷ wkT Γ σ x 

wkvar : {Γ : Ctx} {σ : VType} →
        (x : Fin (suc (length Γ))) →
        {τ : VType} → τ ∈ Γ → τ ∈ wkT Γ σ x
wkvar zero y = there y
wkvar (suc x) (here' refl) = here' refl
wkvar (suc x) (there y) = there (wkvar x y) 


mutual
  wkV : {Γ : Ctx} {σ τ : VType} →
        (x : Fin (suc (length Γ))) →
        VTerm Γ τ → VTerm (wkT Γ σ x) τ
  wkV x TT = TT
  wkV x FF = FF
  wkV x ZZ = ZZ
  wkV x (SS t) = SS (wkV x t)
  wkV x ⟨ t , t' ⟩ = ⟨ wkV x t , wkV x t' ⟩
  wkV x (FST t) = FST (wkV x t)
  wkV x (SND t) = SND (wkV x t)
  wkV x (VAR x') = VAR (wkvar x x')
  wkV x (LAM σ t) = LAM σ (wkC (suc x) t)
  wkV x (VCAST t p) = VCAST (wkV x t) p

  
  wkC : {Γ : Ctx} {σ : VType} {τ : CType} →
        (x : Fin (suc (length Γ))) →
        CTerm Γ τ → CTerm (wkT Γ σ x) τ
  wkC x (VAL y) = VAL (wkV x y) 
  wkC x (FAIL σ) = FAIL σ
  wkC x (TRY t WITH t') = TRY (wkC x t) WITH (wkC x t')
  wkC x (IF b THEN t ELSE t') = IF (wkV x b) THEN (wkC x t) ELSE (wkC x t')
  wkC x (t $ u) = wkV x t $ wkV x u
  wkC x (PREC y t t' p) = PREC (wkV x y) (wkC x t) (wkC (suc (suc x)) t') p
  wkC x (LET t IN t') = LET (wkC x t) IN (wkC (suc x) t')
  wkC x (CCAST t p) = CCAST (wkC x t) p 

{-
mutual
  ctrV : {Γ : Ctx} {σ τ : VType} → VTerm (σ ∷ σ ∷ Γ) τ → VTerm (σ ∷ Γ) τ
  ctrV TT = TT
  ctrV FF = FF
  ctrV ZZ = ZZ
  ctrV (SS t) = SS (ctrV t)
  ctrV ⟨ t , t' ⟩ = ⟨ ctrV t , ctrV t' ⟩
  ctrV (FST t) = FST (ctrV t)
  ctrV (SND t) = SND (ctrV t)
  ctrV (VAR (here' x)) = VAR (here' x)
  ctrV (VAR (there x)) = VAR x
  ctrV (LAM σ t) = {!!}
  ctrV (VCAST t p) = VCAST (ctrV t) p

  ctrC : {Γ : Ctx} {σ : VType} {τ : CType} → CTerm (σ ∷ σ ∷ Γ) τ → CTerm (σ ∷ Γ) τ
  ctrC (VAL x) = VAL (ctrV x)
  ctrC (FAIL σ) = FAIL σ
  ctrC (TRY t WITH t') = TRY ctrC t WITH ctrC t'
  ctrC (IF x THEN t ELSE t') = IF ctrV x THEN ctrC t ELSE ctrC t'
  ctrC (t $ t') = ctrV t $ ctrV t'
  ctrC (PREC x t t' p) = PREC (ctrV x) (ctrC t) {!!} p
  ctrC (LET t IN t') = LET ctrC t IN {!!}
  ctrC (CCAST t p) = CCAST (ctrC t) p

-}


wk : {Γ : Ctx} → ⟪ Γ ⟫x →
     {σ : VType} → ⟪ σ ⟫v →
     (x : Fin (suc (length Γ))) → ⟪ wkT Γ σ x ⟫x 
wk ρ v zero =  v , ρ
wk {[]} tt v (suc x) = v , tt
wk {_ ∷ _} (w , ρ) v (suc x) = w , wk ρ v x

lemmaVar : {Γ : Ctx} (ρ : ⟪ Γ ⟫x) →
           {σ : VType} (v : ⟪ σ ⟫v) →
           (x : Fin (suc (length Γ))) →
           {τ : VType} (y : τ ∈  Γ) →
           proj (wkvar x y) (wk ρ v x) ≡ proj y ρ
lemmaVar ρ v zero y = refl
lemmaVar ρ v (suc x) (here' refl) = refl
lemmaVar (_ , ρ) v (suc x) (there y) = lemmaVar ρ v x y

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v w z} → x ≡ y → u ≡ v → w ≡ z → f x u w ≡ f y v z
cong₃ f refl refl refl = refl


mutual 
  lemmaV : {Γ : Ctx} (ρ : ⟪ Γ ⟫x) →
           {σ : VType} (v : ⟪ σ ⟫v) →
           (x : Fin (suc (length Γ))) →
           {τ : VType} (t : VTerm Γ τ) →
           ⟦ wkV x t ⟧v (wk ρ v x) ≡ ⟦ t ⟧v ρ
  lemmaV ρ v x TT = refl
  lemmaV ρ v x FF = refl
  lemmaV ρ v x ZZ = refl
  lemmaV ρ v x (SS t) = cong suc (lemmaV ρ v x t)
  lemmaV ρ v x ⟨ t , u ⟩ = cong₂ _,_ (lemmaV ρ v x t) (lemmaV ρ v x u)
  lemmaV ρ v x (FST t) = cong proj₁ (lemmaV ρ v x t)
  lemmaV ρ v x (SND t) = cong proj₂ (lemmaV ρ v x t)
  lemmaV ρ v x (VAR y) = lemmaVar ρ v x y
  lemmaV ρ v x (LAM σ t) = funext (λ z → ⟦ wkC (suc x) t ⟧c (z , wk ρ v x))
                                  (λ z → ⟦ t ⟧c (z , ρ))
                                  (λ z → lemmaC (z , ρ) v (suc x) t)
  lemmaV ρ v x (VCAST t p) = cong (vcast p) (lemmaV ρ v x t)


  lemmaC : {Γ : Ctx} (ρ : ⟪ Γ ⟫x) →
           {σ : VType} (v : ⟪ σ ⟫v) →
           (x : Fin (suc (length Γ))) →
           {τ : CType} (t : CTerm Γ τ) →
           ⟦ wkC x t ⟧c (wk ρ v x) ≡ ⟦ t ⟧c ρ
  lemmaC ρ v x (VAL x') = cong η (lemmaV ρ v x x')
  lemmaC ρ v x (FAIL σ) = refl
  lemmaC ρ v x (TRY_WITH_ {e} {e'} t t') = cong₂ (sor e e') (lemmaC ρ v x t) (lemmaC ρ v x t')
  lemmaC ρ v x (IF_THEN_ELSE_ {e} {e'} b t t')
    rewrite lemmaV ρ v x b | lemmaC ρ v x t | lemmaC ρ v x t' = refl
{- alternative without rewrite
  lemmaC ρ v x (IF_THEN_ELSE_ {e} {e'} b t t') =
    cong₃ (λ b t f → if b then (sub (lub e e') t) else (sub (lub-sym e' e) f))
          (lemmaV ρ v x b) (lemmaC ρ v x t) (lemmaC ρ v x t') -}
  lemmaC ρ v x (f $ x') rewrite lemmaV ρ v x f | lemmaV ρ v x x' = refl
  lemmaC ρ v x (PREC y t t' p) =
    cong₃ (λ n z s → primrecT n z s p)
          (lemmaV ρ v x y) (lemmaC ρ v x t)
          (funext (λ i acc → ⟦ wkC (suc (suc x)) t' ⟧c (acc , i , wk ρ v x))
                  (λ i acc → ⟦ t' ⟧c (acc , i , ρ))
                  (λ i → funext (λ acc → ⟦ wkC (suc (suc x)) t' ⟧c (acc , i , wk ρ v x))
                                 (λ acc → ⟦ t' ⟧c (acc , i , ρ))
                                 (λ acc → lemmaC (acc , i , ρ) v (suc (suc x)) t')))
  lemmaC ρ v x (LET_IN_ {e} {e'} t t') rewrite lemmaC ρ v x t  =
    cong (λ f → lift {e} {e'} f (⟦ t ⟧c ρ))
         (funext (λ w → ⟦ wkC (suc x) t' ⟧c (w , wk ρ v x))
                 (λ w → ⟦ t' ⟧c (w , ρ))
                 (λ w → lemmaC (w , ρ) v (suc x) t'))
  lemmaC ρ v x (CCAST t p) = cong (ccast p) (lemmaC ρ v x t)


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


{-
dup-comp' : {Γ : Ctx} {X Y : VType} {e : Exc}
            (m : CTerm Γ (errok / X)) (n : CTerm (X ∷ X ∷ Γ) (e / Y)) →
            ⟦ LET m IN LET wkC zero m IN ? ⟧c ≡ ⟦ LET m IN n ⟧c
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

