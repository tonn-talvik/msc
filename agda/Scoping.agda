module Scoping where

open import Data.Empty
open import Data.Unit renaming (tt to top) 
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat renaming (_≟_ to _=N?_) 

open import Relation.Nullary

data _∈_ {A : Set}(x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

lemma0 : (x : ℕ) → ¬ (x ∈ [])
lemma0 x ()

lemma1 : (x y : ℕ) → (xs : List ℕ) → ¬ (x ≡ y) → ¬ (x ∈ xs) → ¬ (x ∈ (y ∷ xs))
lemma1 .y y xs ¬p ¬q here = ¬p refl
lemma1 x y xs ¬p ¬q (there r) = ¬q r 

_∈?_ : (x : ℕ) → (xs : List ℕ) → Dec (x ∈ xs) 
x ∈? [] =  no ((lemma0 x))
x ∈? (y ∷ xs) with x =N? y 
x ∈? (y ∷ xs) | yes p rewrite p =  yes here
x ∈? (y ∷ xs) | no ¬p with x ∈? xs 
x ∈? (y ∷ xs) | no ¬p | yes q =  yes (there q)
x ∈? (y ∷ xs) | no ¬p | no ¬q =  no (lemma1  x y xs ¬p ¬q)


truncate : {P : Set} → Dec P → Set
truncate (yes _) = ⊤
truncate (no  _) = ⊥


extract : {P : Set} → {d : Dec P} → truncate d → P
extract {_} {yes p} t = p
extract {_} {no ¬p} ()





list = 13 ∷ 17 ∷ 42 ∷ 3 ∷ []


data nicenumber : Set where
  N : (n : ℕ) → { _ : truncate (n ∈? list) } → nicenumber


nice2nat : (n : nicenumber) → ℕ
nice2nat (N n) = n

nice2inlist : (n : nicenumber) → nice2nat n ∈ list
nice2inlist (N n {t}) =  extract t


seventeen : nicenumber
seventeen = N 17
twelve : nicenumber
twelve = N 12

