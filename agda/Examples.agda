module Examples where

open import Data.Bool hiding (T)
open import Data.List
open import Data.Nat
open import Data.Unit
open import Data.Product

open import Finiteness
open import Language
open import Semantics

----------------------------------------------------------------------
-- Silly examples

pv0      = ⟦ VAL (LAM nat (VAL (varify 0))) ⟧ tt
--pv0-contra = ⟦ VAL (LAM nat (VAL (varify 1))) ⟧ tt
pv1        = ⟦ VAL (varify 0) ⟧ (1 , tt)
--pv1-contra = ⟦ VAL (varify 1) ⟧ (1 , tt)
pv2        = ⟦ IF (varify 2) THEN VAL (varify 0) ELSE VAL (varify 1) ⟧ (1 , 2 , false , tt)
pv3 : {Γ : Ctx} → ⟦ nat ∷ Γ ⟧l →  T ℕ
pv3        = ⟦ VAL (varify 0) ⟧

-- http://mazzo.li/posts/Lambda.html builds variable proofs during type checking
-- data Syntax : Set where
--   var : ℕ → Syntax
-- data Term {n} {Γ : Ctx n) : Type → Set where
--   var : ∀ {τ} (v : Fin n) → τ ≡ lookup v Γ → Term Γ τ

----------------------------------------------------------------------

p1 = ⟦ VAL (varify 0) ⟧ (1 , tt)
p2 = ⟦ IF TT THEN (VAL (SS ZZ)) ELSE VAL ZZ ⟧ tt
p3 = ⟦ (varify 0) $ (varify 1) ⟧ ( (λ x → η (x * x)) , (3 , tt) ) 
p4 = ⟦ VAL (SND ⟨ ZZ , TT ⟩ ) ⟧ tt
p5 = ⟦ LAM nat (VAL (SS (varify 0))) $ ZZ ⟧ tt
p6 = ⟦ PREC (natify 6) (VAL ZZ) ((LET VAL (varify 0) IN (VAL (varify 1)) )) ⟧ tt
p7 : ℕ → T ℕ
p7 n  = ⟦ PREC (natify n) (VAL ZZ) (CHOOSE (VAL (varify 0)) (VAL (SS (SS (varify 0))))) ⟧ tt

-----------------------------------------------------------------

INC  : ∀ {Γ} → VTerm Γ (nat ⇒ nat)
INC = LAM nat (VAL (SS (VAR here)))

test-inc-75 = ⟦ INC $ natify 75 ⟧ tt


IS-ZERO : ∀ {Γ} → VTerm Γ (nat ⇒ bool)
IS-ZERO = LAM nat
              (PREC (VAR here)
                    (VAL TT)
                    (VAL FF))

test-is-zero = ⟦ IS-ZERO $ natify 0 ⟧ tt


DEC : ∀ {Γ} → VTerm Γ (nat ⇒ nat)
DEC = LAM nat (LET PREC (VAR here)
                        (VAL ⟨ ZZ , TT ⟩)
                        (IF (SND (VAR here)) THEN
                           VAL ⟨ ZZ , FF ⟩ 
                         ELSE
                           VAL ⟨ SS (FST (VAR here)) , FF ⟩
                        )
                   IN VAL (FST (VAR here)) )
                   
test-dec = ⟦ DEC $ natify 10 ⟧ tt


ADD : ∀ {Γ} → VTerm Γ (nat ⇒ nat ⇒ nat)
ADD = (LAM nat (
          VAL (LAM nat
               (PREC (varify 0)
                     (VAL (varify 1))
                     (VAL (SS (varify 0)))))))

test-add-3-4 = ⟦ LET ADD $ varify 1 IN varify 0 $ varify 1 ⟧ (3 , (4 , tt))


MUL : ∀ {Γ} → VTerm Γ (nat ⇒ nat ⇒ nat)
MUL = (LAM nat (
          VAL (LAM nat
               (PREC (varify 0)
                     (VAL ZZ)
                     (LET ADD $ varify 0 IN
                          (varify 0 $ varify 4 ))))))

test-mul-3-4 = ⟦ LET MUL $ natify 3 IN varify 0 $ natify 4 ⟧ tt



FACT : ∀ {Γ} → VTerm Γ (nat ⇒ nat)
FACT = LAM nat
           (PREC (VAR here)
                 (VAL (SS ZZ))
                 (LET MUL $ VAR here IN
                      (VAR here $ SS (VAR (there (there here))))))
                      
test-fact-5 = ⟦ FACT $ natify 5 ⟧ tt


------------------------------------------------------------

NOT : ∀ {Γ} → VTerm Γ (bool ⇒ bool)
NOT = LAM bool (IF VAR here THEN VAL FF ELSE VAL TT)

AND OR : ∀ {Γ} → VTerm Γ (bool ⇒ bool ⇒ bool)
AND = LAM bool (VAL (LAM bool
        (IF VAR here THEN
          (IF VAR (there here) THEN
            VAL TT
          ELSE
            VAL FF)
        ELSE
          VAL FF
        )))

OR = LAM bool (VAL (LAM bool (IF VAR here THEN VAL TT ELSE IF VAR (there here) THEN VAL TT ELSE VAL FF)))

test-and = ⟦ LET AND $ TT IN varify 0 $ TT ⟧ tt


-- infinite program in my language
-- inf : ∀ {Γ} → CTerm Γ nat
-- inf = LET inf IN VAL (VAR here)
