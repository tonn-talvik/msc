{-# OPTIONS --type-in-type #-}

module Finiteness where


open import Data.Empty
open import Data.Unit renaming (tt to top) 
open import Data.List
open import Data.List.All


open import Data.List

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

infix 5 _∈_ 

data _∈_ {X : Set} : X → List X → Set where
  here : {x : X} → {xs : List X} → x ∈ (x ∷ xs)
  there : {x x' : X} → {xs : List X} → x ∈ xs → x ∈ x' ∷ xs
 
  
record Listable (X : Set) : Set where
  constructor _,_
  field 
    list : List X
    complete : (x : X) → x ∈ list


data ND : Set where
  nd0  : ND
  nd01 : ND
  nd1  : ND
  nd1+ : ND
  ndN  : ND

listND : List ND
listND = nd0 ∷ nd01 ∷ nd1 ∷ nd1+ ∷ ndN ∷ [] 

cmpltND : (x : ND) → x ∈ listND
cmpltND nd0 = here
cmpltND nd01 = there here
cmpltND nd1 = there (there here)
cmpltND nd1+ = there (there (there here))
cmpltND ndN = there (there (there (there here)))


lstblND : Listable ND 
lstblND = record { list = listND
                 ; complete = cmpltND
                 }

DecEq : Set → Set 
DecEq X = (x x' : X) → Dec (x ≡ x')

DecEqFun : (X Y : Set) → Set
DecEqFun X Y = (f g : X → Y) → Dec ((x : X) → f x ≡ g x)


FunExt : (X Y : Set) → Set
FunExt X Y = (f g : X → Y) → ((x : X) → f x ≡ g x) → f ≡ g

postulate funext : {X Y : Set} → FunExt X Y

deceqfunext : {X Y : Set} → DecEqFun X Y → DecEq (X → Y)
deceqfunext p f g with p f g 
deceqfunext p f g | yes q =  yes (funext f g q) 
deceqfunext p f g | no  q =  no ( λ r → q ( λ x → cong (λ h → h x) {f} {g} r))


truncate : {P : Set} → Dec P → Set
truncate (yes _) = ⊤
truncate (no  _) = ⊥


extract : {P : Set} → {d : Dec P} → truncate d → P
extract {_} {yes p} t = p
extract {_} {no ¬p} ()



lstbl2deceq : {X : Set} → Listable X → DecEq X
lstbl2deceq (l , c) x x' with c x | c x'
lstbl2deceq (.(x ∷ xs) , c) x .x | here {.x} {xs} | here =  yes refl
lstbl2deceq (.(x ∷ xs) , c) x x' | here {.x} {xs} | there p' = {!!}
lstbl2deceq (.(x'' ∷ xs) , c) x x' | there {.x} {x''} {xs} p | p' = {!!}



lemma1 : {X : Set} → (P : X → Set) → (p : Listable X) → 
         let open Listable in All P (list p) → (x : X) → P x
lemma1 = {!!}
 

lemma2 : {X : Set} → (P : X → Set) → ((x : X) → Dec (P x)) → ((xs : List X) → Dec (All P xs)) 
lemma2 = {!!} 

powertopeople : {X Y : Set} → Listable X → DecEq Y → DecEqFun X Y
powertopeople (lst , cmpl) (_≡?_) f g = {!!} 
   -- vaja rakendada lemmasid, võttes P x = f x ≡ g x
