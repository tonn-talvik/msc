{-# OPTIONS --type-in-type #-}

module Finiteness where


open import Data.Unit  
open import Data.Product
open import Data.Empty
open import Data.Sum

open import Data.Product

open import Data.List
open import Data.Nat
open import Data.Fin

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_] ; inspect )


infix 5 _∈_ 

data _∈_ {X : Set} (x : X) : List X → Set where
  here' : {x' : X} → {xs : List X} → x' ≡ x → x ∈ (x' ∷ xs)
  there : {x' : X} → {xs : List X} → x ∈ xs → x ∈ (x' ∷ xs)

here : {X : Set} → {x : X} → {xs : List X} → x ∈ (x ∷ xs)
here = here' refl


idx : {X : Set} → {xs : List X} → {x : X} → x ∈ xs → Fin (length xs)
idx (here' p) = zero
idx (there p) = suc (idx p)


lkp : {X : Set} → (xs : List X) → Fin (length xs) → X
lkp [] ()
lkp (x ∷ xs) zero = x
lkp (x ∷ xs) (suc n) = lkp xs n


lkpcorrect : {X : Set} → (xs : List X) → {x : X} → (p : x ∈ xs) → lkp xs (idx p) ≡ x
lkpcorrect .(x' ∷ xs) (here' {x'} {xs} p) = p
lkpcorrect .(x' ∷ xs) (there {x'} {xs} p) = lkpcorrect xs p


trace : {X : Set} (xs : List X) (n : Fin (length xs)) → lkp xs n ∈ xs
trace [] ()
trace (x ∷ xs) zero = here
trace (x ∷ xs) (suc n) = there (trace xs n)


_≡F_ : {n : ℕ} → Fin n → Fin n → Set
i ≡F j = i ≡ j

peano4 : {n : ℕ} → (i : Fin n) → zero ≡F suc i → ⊥
peano4 i ()

peano5 : {n : ℕ} → (i j : Fin n) → suc i ≡F suc j → i ≡ j
peano5 i .i refl = refl

_?≡F_ : {n : ℕ} → (i j : Fin n) → Dec (i ≡ j)
zero ?≡F zero = yes refl
zero ?≡F suc j =  no (peano4 j)
suc i ?≡F zero =  no ( λ p → peano4 i (sym p))
suc i ?≡F suc j with i ?≡F j 
... | yes p = yes (cong suc p)
... | no ¬p = no (λ p → ¬p (peano5 i j p))


record Listable (X : Set) : Set where
  constructor _£_
  field 
    list : List X
    complete : (x : X) → x ∈ list
    

idxinj : {X : Set} → (p : Listable X) → let open Listable p in 
       {x y : X} → idx (complete x) ≡ idx (complete y) → x ≡ y
idxinj (list £ complete) {x} {y} p = 
  trans (sym (lkpcorrect list (complete x))) 
        (trans (cong (lkp list) p) (lkpcorrect list (complete y))) 


?≡L : {X : Set} → Listable X → (x y : X) → Dec (x ≡ y) 
?≡L (list £ complete) x y with idx (complete x) ?≡F idx (complete y) 
?≡L (list £ complete) x y | yes p = yes (idxinj (list £ complete) p)
?≡L (list £ complete) x y | no ¬p = no ( λ p → ¬p (cong (λ x → idx (complete x)) p))


All : {X : Set} → (xs : List X) → (P : X → Set) → Set
All {X} xs P = {x : X} → x ∈ xs → P x

?All : {X : Set} → {P : X → Set} → (xs : List X) → 
                          ((x : X) → Dec (P x)) → Dec (All xs P) 
?All []       f =  yes (λ ())
?All (x ∷ xs) f with f x 
?All (x ∷ xs) f | yes p with ?All xs f
?All (x ∷ xs) f | yes p | yes p' = yes (λ { (here' q) → subst _ q p 
                                        ; (there q) → p' q })
?All (x ∷ xs) f | yes p | no ¬p' =  no (λ q → ¬p' (λ r → q (there r))) 
?All (x ∷ xs) f | no ¬p = no (λ q → ¬p (q here)) 


Some : {X : Set} → (xs : List X) → (P : X → Set) → Set
Some {X} xs P = Σ X (λ x → x ∈ xs × P x)

?Some : {X : Set} → {P : X → Set} → (xs : List X) → 
                          ((x : X) → Dec (P x)) → Dec (Some xs P) 
?Some []       f = no ( λ { (_ , () , _) }) 
?Some (x ∷ xs) f with f x 
?Some (x ∷ _ ) f | yes p =  yes (x , here , p)
?Some (_ ∷ xs) f | no ¬p with ?Some xs f
?Some (_ ∷ _ ) f | no _  | yes (x' , q , p') = yes (x' , there q , p')
?Some (x ∷ _ ) f | no ¬p | no ¬p'            = 
     no  ( λ { (.x , here' refl , p) → ¬p p 
             ; (y  , there q    , p) → ¬p' (y , q , p) } )



?∀ : {X : Set} → (p : Listable X) → {P : X → Set} 
       → ((x : X) → Dec (P x)) → Dec ((x : X) → P x)
?∀ (list £ complete) f with ?All list f 
... | yes q = yes (λ x → q (complete x))
... | no ¬q = no (λ g → ¬q (λ {x} → λ _ → g x)) 

?∃ : {X : Set} → (p : Listable X) → {P : X → Set} 
       → ((x : X) → Dec (P x)) → Dec (Σ X P)
?∃ (list £ complete) f with ?Some list f 
... | yes (x , _ , p) = yes (x , p)
... | no ¬q = no ( λ { (x , p) →  ¬q (x , complete x , p)  })



?⊤ : Dec ⊤ 
?⊤ = yes tt

_?×_ : {P Q : Set} → Dec P → Dec Q → Dec (P × Q)
yes p ?× yes q = yes (p , q)
_     ?× no ¬q = no (λ {(_ , q) → ¬q q}) 
no ¬p ?× _     = no (λ {(p , _) → ¬p p}) 


?⊥ : Dec ⊥
?⊥ = no (λ ())

_?⊎_ : {P Q : Set} → Dec P → Dec Q → Dec (P ⊎ Q)
yes p ?⊎ q     = yes (inj₁ p)
_     ?⊎ yes q = yes (inj₂ q)
no ¬p ?⊎ no ¬q = no (λ {(inj₁ p) → ¬p p ; (inj₂ q) → ¬q q}) 


_?→_ : {P Q : Set} → Dec P → Dec Q → Dec (P → Q)
_     ?→ yes q = yes (λ _ → q)
no ¬p ?→ _     = yes (λ p → ⊥-elim (¬p p)) 
yes p ?→ no ¬q = no  (λ r → ¬q (r p))


truncate : {P : Set} → Dec P → Set
truncate (yes _) = ⊤
truncate (no  _) = ⊥


extract : {P : Set} → (d : Dec P) → {_ : truncate d} → P
extract (yes p) {_} = p
extract (no ¬p) {()}



-- this material is not used currently


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



data Inspect {A : Set}(x : A) : Set where
  it : (y : A) →  x ≡ y →  Inspect x

inspect : {A : Set}(x : A) → Inspect x
inspect x = it x refl


cong' : {A : Set} {B : A → Set}
       (f : (x : A) → B x) → {x y : A} → (p : x ≡ y) → subst B p (f x) ≡ f y
cong' f refl = refl

