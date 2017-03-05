module MyExpressions where

open import Data.Nat renaming (ℕ to Nat)

open import MyTypes

infixl 80 _$_
data Raw : Set where
  var : Nat -> Raw
  _$_ : Raw -> Raw -> Raw
  lam : Type -> Raw -> Raw
