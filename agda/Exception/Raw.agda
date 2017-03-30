module Raw where

open import Data.Nat
open import Exception

infixl 90 _$_
infix  80 _/_
infixr 70 _⟹_
infix  60 _∏_



mutual -- value and computation types
  data VType : Set where
    nat : VType
    bool : VType
    _∏_ : VType → VType → VType
    _⟹_ : VType → CType → VType

  data CType : Set where
    _/_ : Exc → VType → CType

{-
-- really green types
data Type : Set where
  nat : Type
  bool : Type
  _π_ : Type → Type → Type
  _⇒_ : Type → Type → Type
-}

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
    VAL : vTerm → cTerm -- superfluous
    FAIL : VType → cTerm
    TRY_WITH_ : cTerm → cTerm → cTerm
    IF_THEN_ELSE_ : vTerm → cTerm → cTerm → cTerm
    _$_ : vTerm → vTerm → cTerm
    PREC : vTerm → cTerm → cTerm → cTerm
    LET_IN_ : cTerm → cTerm → cTerm
