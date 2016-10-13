{-# OPTIONS --type-in-type #-}

module Finiteness where


open import Data.Empty
open import Data.Unit renaming (tt to top) 
open import Data.List
--open import Data.List.All

open import Data.Product

open import Data.List

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_] ; inspect )


infix 5 _∈_ 

data _∈_ {X : Set} : X → List X → Set where
  here : {x : X} → {xs : List X} → x ∈ (x ∷ xs)
  there : {x x' : X} → {xs : List X} → x ∈ xs → x ∈ (x' ∷ xs)

here≠there : {X : Set} → (x : X) → {xs : List X} → (p : x ∈ xs) → here {_} {x} {xs} ≡ there {_} {x} {x} {xs} p → ⊥
here≠there x _ ()



All : {A : Set} → (P : A → Set) (xs : List A) → Set
All {A} P xs = {x : A} → x ∈ xs → P x

{-  
data All {A : Set}
         (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

    
lookup : {A : Set} {P : A → Set} {xs : List A} →
         All P xs → {x : A} → x ∈ xs → P x
lookup []         ()
lookup (px ∷ pxs) here  = px
lookup (px ∷ pxs) (there q) = lookup pxs q
-}

record Listable (X : Set) : Set where
  constructor _,_
  field 
    list : List X
    complete : (x : X) → x ∈ list



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
deceqfunext p f g | no ¬q =  no ( λ r → ¬q ( λ x → cong (λ h → h x) {f} {g} r))


truncate : {P : Set} → Dec P → Set
truncate (yes _) = ⊤
truncate (no  _) = ⊥


extract : {P : Set} → (d : Dec P) → {_ : truncate d} → P
extract {_} (yes p) {t} = p
extract {_} (no ¬p) {()}


--lemma-different-points : {X Y : Set} → {x y : X} → (f : X → Y)


data Inspect {A : Set}(x : A) : Set where
  it : (y : A) →  x ≡ y →  Inspect x

inspect : {A : Set}(x : A) → Inspect x
inspect x = it x refl


cong' : {A : Set} {B : A → Set}
       (f : (x : A) → B x) → {x y : A} → (p : x ≡ y) → subst B p (f x) ≡ f y
cong' f refl = refl



lemmaA : {X : Set} → (p : Listable X) → let open Listable p in {x y : X}  
       → (r : x ≡ y) → (subst (λ x → x ∈ list) r (complete x) ≡ complete y → ⊥) → ⊥ 
lemmaA (lstbl , cmpl) refl f = f (cong' cmpl refl)


{-
-- Hint: Fin.Finiteness:lstblEq
lstbl2deceq : {X : Set} → Listable X → DecEq X
lstbl2deceq (xs , p) x y with inspect (p x) | inspect (p y) 
lstbl2deceq (.(_ ∷ _) , p) x .x | it here _  | it here _  = yes refl
lstbl2deceq ((.x ∷ xs) , p) x y | it here  u | it (there q) v  =  no ( λ r →  here≠there y q (subst (λ x → _ ∈ x ∷ _) r (trans {!!} {!v!} ))  )  -- here≠there q (trans (trans (sym (subst _ r u)) (cong p r)) v)
lstbl2deceq (.(_ ∷ _) , p) x y | it (there q) u | it here v   = {! no ?!} 
lstbl2deceq (.(_ ∷ _) , p) x y | it (there q) u | it (there q') v  = {! no ?!} 
-}



--trivial : {X : Set} → {x : X} → ¬ x ∈ [] 
--trivial ()

lemma1 : {X : Set} → (p : Listable X) → {P : X → Set} → 
         All P (Listable.list p) → (x : X) → P x
lemma1 p f x = f (Listable.complete p x)


lemma20 : {X : Set} → {P : X → Set} → (x : X) → (xs : List X) → P x → All P xs → All P (x ∷ xs)
lemma20 x xs p f (here) = p
lemma20 x xs p f (there q) = f q

lemma2 : {X : Set} → {P : X → Set} →
         ((x : X) → Dec (P x)) → ((xs : List X) → Dec (All P xs)) 
lemma2 f [] = yes (λ ())
lemma2 f (x ∷ xs) with f x 
...               | yes p with lemma2 f xs 
...                       | yes p' = yes (lemma20 x xs p p')
...                       | no ¬p' = no ( λ q → ¬p' ( λ r → q (there r)) ) 
lemma2 f (x ∷ xs) | no ¬p = no ( λ q → ¬p (q here) ) 


?∀ : {X : Set} → (p : Listable X) → {P : X → Set} →
     ((x : X) → Dec (P x)) → Dec ((x : X) → P x)
?∀ p f with lemma2 f (Listable.list p) 
... | yes q = yes (lemma1 p q)
... | no ¬q = no (λ g → ¬q ( λ {x} → λ _ → g x )) 


_?∧_ : {P Q : Set} →
       Dec P → Dec Q → Dec (P × Q)
(yes p) ?∧ (yes q) = yes (p , q)
(yes p) ?∧ (no ¬q) = no ( λ { (p , q) → ¬q q } ) 
(no ¬p) ?∧ q = no ( λ { (p , q) → ¬p p } ) 

_?→_ : {P Q : Set} →
        Dec P → Dec Q → Dec (P → Q)
_       ?→ (yes q) = yes (λ _ → q)
(no ¬p) ?→ _ = yes (λ p → ⊥-elim (¬p p) ) 
(yes p) ?→ (no ¬q) = no ( λ r →  ¬q ( r p) )


--powertopeople : {X Y : Set} → Listable X → DecEq Y → DecEqFun X Y
--powertopeople (lst , cmpl) (_≡?_) f g = {!!} 
   -- vaja rakendada lemmasid, võttes P x = f x ≡ g x
