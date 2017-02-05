module Examples where

open import Data.Bool hiding (T)
open import Data.List
open import Data.Nat
open import Data.Unit
open import Data.Product

open import Relation.Binary.Core using (_≡_ ; refl)

open import Finiteness
open import Language
open import Semantics

----------------------------------------------------------------------
-- Silly examples for variables

test-v0      = ⟦ VAL (LAM nat (VAL (varify 0))) ⟧ tt
--test-v0-contra = ⟦ VAL (LAM nat (VAL (varify 1))) ⟧ tt
testv1        = ⟦ VAL (varify 0) ⟧ (1 , tt)
--test-v1-contra = ⟦ VAL (varify 1) ⟧ (1 , tt)
test-v2        = ⟦ IF (varify 2) THEN VAL (varify 0) ELSE VAL (varify 1) ⟧ (1 , 2 , false , tt)
test-v3 : {Γ : Ctx} → ⟦ nat ∷ Γ ⟧l →  T ℕ
test-v3        = ⟦ VAL (varify 0) ⟧


test-p1 = ⟦ VAL (varify 0) ⟧ (1 , tt)
test-p2 = ⟦ IF TT THEN (VAL (SS ZZ)) ELSE VAL ZZ ⟧ tt
test-p3 = ⟦ (varify 0) $ (varify 1) ⟧ ( (λ x → η (x * x)) , (3 , tt) ) 
test-p4 = ⟦ VAL (SND ⟨ ZZ , TT ⟩ ) ⟧ tt
test-p5 = ⟦ LAM nat (VAL (SS (varify 0))) $ ZZ ⟧ tt
test-p6 = ⟦ PREC (natify 6) (VAL ZZ) ((LET VAL (varify 0) IN (VAL (varify 1)) )) ⟧ tt
test-p7 : ℕ → T ℕ
test-p7 n  = ⟦ PREC (natify n) (VAL ZZ) (CHOOSE (VAL (varify 0)) (VAL (SS (SS (varify 0))))) ⟧ tt


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
test-or = ⟦ LET OR $ FF IN varify 0 $ TT ⟧ tt
-----------------------------------------------------------------

DEC' : ∀ {Γ} → VTerm Γ (nat ⇒ (nat ∏ bool))
DEC' = LAM nat (PREC (VAR here)
                     (VAL ⟨ ZZ , TT ⟩)
                     (IF (SND (VAR here)) THEN
                        VAL ⟨ ZZ , FF ⟩ 
                      ELSE
                        VAL ⟨ SS (FST (VAR here)) , FF ⟩
                     ))

run-dec':1 = ⟦ DEC' $ natify 1 ⟧ tt


--SUB' = (x - y) ∏ x <? y
SUB' : ∀ {Γ} → VTerm Γ (nat ⇒ nat ⇒ (nat ∏ bool))
SUB' = LAM nat (VAL (LAM nat (PREC (varify 0) -- y
                                   (VAL ⟨ varify 1 , FF ⟩) -- (x,f)
                                   (DEC' $ (FST (varify 0))))))

prg-sub' : {Γ : Ctx} → ⟦ nat ∷ nat ∷ Γ ⟧l  → T (ℕ × Bool)
prg-sub' = ⟦ LET SUB' $ varify 0 IN varify 0 $ varify 2 ⟧

run-sub':31-15 = prg-sub' (31 , (15 , tt))
tst-sub':31-15=16,f : run-sub':31-15 ≡ [ (16 , false) ]
tst-sub':31-15=16,f = refl

run-sub':5-5 = prg-sub' (5 , (5 , tt))
tst-sub':5-5=0,f : run-sub':5-5 ≡ [ (0 , false) ]
tst-sub':5-5=0,f = refl

run-sub':5-6 = prg-sub' (5 , (6 , tt))
tst-sub':5-6=0,t : run-sub':5-6 ≡ [ (0 , true) ]
tst-sub':5-6=0,t = refl

LT EQ GT : ∀ {Γ} → VTerm Γ (nat ⇒ nat ⇒ bool)
LT = LAM nat (VAL (LAM nat (LET SUB' $ varify 1 IN (LET varify 0 $ varify 1 IN VAL (SND (varify 0))))))
EQ = {!!}
GT = LAM nat (VAL (LAM nat (LET SUB' $ varify 0 IN (LET varify 0 $ varify 2 IN VAL (SND (varify 0))))))


prg-lt prg-gt : {Γ : Ctx} → ⟦ nat ∷ nat ∷ Γ ⟧l  → T Bool
prg-lt = ⟦ LET LT $ varify 0 IN varify 0 $ varify 2 ⟧
prg-gt = ⟦ LET GT $ varify 0 IN varify 0 $ varify 2 ⟧

run-lt:4<3 = prg-lt (4 , (3 , tt))
tst-lt:4<3 : run-lt:4<3 ≡ [ false ]
tst-lt:4<3 = refl

run-gt:4>3 = prg-gt (4 , (3 , tt))
tst-gt:4>3 : run-gt:4>3 ≡ [ true ]
tst-gt:4>3 = refl

run-gt:3>4 = prg-gt (3 , (4 , tt))
tst-gt:3>4 : run-gt:3>4 ≡ [ false ]
tst-gt:3>4 = refl

run-gt:3>3 = prg-gt (3 , (3 , tt))
tst-gt:3>3 : run-gt:3>3 ≡ [ false ]
tst-gt:3>3 = refl

-----------------------------------------------------------------

-- infinite program in my language
-- inf : ∀ {Γ} → CTerm Γ nat
-- inf = LET inf IN VAL (VAR here)

-----------------------------------------------------------------

-- Example taken from Nick Benton et al. article
-- "Counting Successes: Effects and Transformations for Non-deterministic Programs"
-- ⟦ ⊢ let f ⇐ val (λx : int. if x < 6 then val x else fail) in
--     let x ⇐ val 1 or val 2 in let y ⇐ val 3 or val 4 in f(x+y) : T int⟧ = {4,5}

run-benton-1 =
  ⟦ LET (VAL (LAM nat                                      -- f ⇐ val (λx: int.
                  (LET (LET LT $ varify 0
                        IN varify 0 $ natify 6)            --          x < 6
                   IN IF varify 0                          --       if ...
                      THEN VAL (varify 1)                  --         then val x
                      ELSE FAIL)))                         --         else fail)
    IN (LET (CHOOSE (VAL (natify 1)) (VAL (natify 2)))     -- x ⇐ val 1 or val 2
        IN (LET (CHOOSE (VAL (natify 3)) (VAL (natify 4))) -- y ⇐ val 3 or val 4
            IN (LET (LET ADD $ varify 1
                     IN (varify 0 $ varify 1))             --  x + y
                IN varify 3 $ varify 0))) ⟧ tt             -- f(...)

tst-benton-1 : run-benton-1 ≡ 4 ∷ 5 ∷ 5 ∷ [] -- our list has duplicates too!
tst-benton-1 = refl
------------------------------------------------------------

test-err = ⟦ VAL (ERR "division by 0") ⟧ tt
