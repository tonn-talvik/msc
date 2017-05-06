module Examples where

open import Data.Nat
open import Data.Unit
open import Data.Vec hiding (here)
open import Relation.Binary.PropositionalEquality

open import Finiteness
open import NonDetBoundedVec
open import Raw
open import Refined
open import Semantics
open import Sugar
open import Types


ADD : ∀ {Γ} → VTerm Γ (nat ⇒ 1 / (nat ⇒ 1 / nat))
ADD = (LAM nat (
          VAL (LAM nat
               (PREC (varify 0)
                     (VAL (varify 1))
                     (VAL (SS (varify 0)))
                     (s≤s z≤n)))))
                     
DEC' : ∀ {Γ} → VTerm Γ (nat ⇒ 1 / (nat ● bool))
DEC' = LAM nat (PREC (VAR here)
                     (VAL ⟨ ZZ , TT ⟩)
                     (IF (SND (VAR here)) THEN
                        VAL ⟨ ZZ , FF ⟩ 
                      ELSE
                        VAL ⟨ SS (FST (VAR here)) , FF ⟩
                     )
                     (s≤s z≤n))


--SUB' = (x - y) ● x <? y
SUB' : ∀ {Γ} → VTerm Γ (nat ⇒ 1 / (nat ⇒ 1 / (nat ● bool)))
SUB' = LAM nat (VAL (LAM nat (PREC (varify 0) -- y
                                   (VAL ⟨ varify 1 , FF ⟩) -- (x,f)
                                   (DEC' $ (FST (varify 0)))
                                   (s≤s z≤n))))


LT GT : ∀ {Γ} → VTerm Γ (nat ⇒ 1 / (nat ⇒ 1 / bool))
LT = LAM nat (VAL (LAM nat (LET SUB' $ varify 1 IN (LET varify 0 $ varify 1 IN VAL (SND (varify 0))))))
GT = LAM nat (VAL (LAM nat (LET SUB' $ varify 0 IN (LET varify 0 $ varify 2 IN VAL (SND (varify 0))))))
-- EQ = {!!} -- AND (not LT) (not GT)

-- Example taken from Nick Benton et al. article
-- "Counting Successes: Effects and Transformations for Non-deterministic Programs"
-- ⟦ ⊢ let f ⇐ val (λx : int. if x < 6 then val x else fail) in
--     let x ⇐ val 1 or val 2 in let y ⇐ val 3 or val 4 in f(x+y) : T int⟧ = {4,5}

run-benton-1 =
  ⟦ LET (VAL (LAM nat                                      -- let f ⇐ val (λx: int.
                  (LET (LET LT $ varify 0
                        IN varify 0 $ natify 6)            --          x < 6
                   IN IF varify 0                          --       if ...
                      THEN VAL (varify 1)                  --         then val x
                      ELSE FAIL nat)))                     --         else fail)
    IN (LET (CHOOSE (VAL (natify 1)) (VAL (natify 2)))     -- let x ⇐ val 1 or val 2
        IN (LET (CHOOSE (VAL (natify 3)) (VAL (natify 4))) -- let y ⇐ val 3 or val 4
            IN (LET (LET ADD $ varify 1
                     IN (varify 0 $ varify 1))             --     x + y
                IN varify 3 $ varify 0))) ⟧C tt             -- in f(...)

tst-benton-1 : run-benton-1 ≡ bv (4 ∷ 5 ∷ 5 ∷ []) (s≤s (s≤s (s≤s z≤n))) -- our list has duplicates too!
tst-benton-1 = refl
