module EExamples where

open import Data.Maybe
open import Data.Nat
open import Data.Unit

open import ELanguage
open import ESemantics

p1 p2 p3 p4 p5 p6 : Maybe ℕ
p1 = ⟦ VAL ZZ ⟧ tt
p2 = ⟦ FAIL ⟧ tt
p3 = ⟦ IF FF THEN VAL (natify 5) ELSE FAIL ⟧ tt
p4 = ⟦ PREC (natify 3) (VAL ZZ) (IF TT THEN VAL (natify 2) ELSE FAIL) ⟧ tt
p5 = ⟦ LET (VAL ZZ) IN (LAM nat (VAL (SS (varify 0)))) $ (varify 0) ⟧ tt
p6 = ⟦ TRY FAIL WITH VAL (natify 3) ⟧ tt
