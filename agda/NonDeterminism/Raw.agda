module Raw where

open import Data.Nat

open import NonDetBoundedVec
open import Types
infixl 90 _$_

mutual
  data vTerm : Set where
    -- booleans
    TT FF : vTerm
    -- naturals
    ZZ : vTerm
    SS : vTerm → vTerm
    -- pairs
    ⟨_,_⟩ : vTerm → vTerm → vTerm
    FST SND : vTerm → vTerm
    -- variables
    VAR : ℕ → vTerm
    -- function abstraction
    LAM : VType → cTerm → vTerm

  data cTerm : Set where
    VAL : vTerm → cTerm
    FAIL : VType → cTerm
    CHOOSE : cTerm → cTerm → cTerm
    IF_THEN_ELSE_ : vTerm → cTerm → cTerm → cTerm
    _$_ : vTerm → vTerm → cTerm
    PREC : vTerm → cTerm → cTerm → cTerm
    LET_IN_ : cTerm → cTerm → cTerm
