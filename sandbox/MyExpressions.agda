module MyExpressions where

open import Data.Nat renaming (ℕ to Nat; _*_ to _n*_) 

open import MyTypes

infixl 80 _$_ _*_
data Raw : Set where
  var : Nat → Raw
  _$_ : Raw → Raw → Raw
  lam : Type → Raw → Raw
  _*_ : Raw → Raw → Raw
  fst : Raw → Raw
  snd : Raw → Raw
  


