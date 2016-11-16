module NonDetVec where

--open import Function
--open import Data.List
--open import Relation.Nullary


--open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality hiding ([_]; inspect)

--open import Finiteness
open import OrderedMonoid
open import GradedMonad

open import Data.Nat
open import Data.Vec

open ≡-Reasoning


ru+ : {n : ℕ} → n + 0 ≡ n
ru+ {zero} = refl
ru+ {suc n} = cong suc (ru+ {n}) 

lu* : {n : ℕ} → 1 * n ≡ n
lu* = ru+ 

ru* : {n : ℕ} → n ≡ n * 1 
ru* {zero} = refl
ru* {suc n} = cong suc (ru* {n})

ass+ : {m n o : ℕ} → (m + n) + o ≡ m + (n + o)
ass+ = {!!}

dist+ : {m n o : ℕ} → (m + n) * o ≡ m * o + n * o
dist+ {zero}  {_} {_} = refl
dist+ {suc m} {n} {o} = trans (cong (_+_ o) (dist+ {m} {n} {o})) 
                              (sym (ass+ {o} {m * o} {n * o}))

ass* : {m n o : ℕ} → (m * n) * o ≡ m * (n * o)
ass* {zero} = refl
ass* {suc m} = {!!}


ℕ* : OrderedMonoid
ℕ* = record { M = ℕ
             ; _⊑_ = _≡_
             ; reflM = refl
             ; transM = trans
             ; i = 1
             ; _·_ = _*_
             ; mon = cong₂ _*_
             ; lu = lu* 
             ; ru =  ru* 
             ; ass = λ {m n o} → ass* {m} {n} {o}
             }

open OrderedMonoid.OrderedMonoid ℕ*
 
ηV : {X : Set} → X → Vec X 1
ηV x = x ∷ [] 



liftV : {m n : ℕ} {X Y : Set} →
        (X → Vec Y n) → Vec X m → Vec Y (m * n)
liftV f [] =  []
liftV f (x ∷ xs) =  f x ++ liftV f xs


subV : {n n' : ℕ} {X : Set} → n ≡ n' → Vec X n → Vec X n'
--subV {X = X} p = subst (Vec X) p
--subV refl xs = xs
subV  = subeq {ℕ} {λ n X → Vec X n}

{-
subV∷ : {m n : ℕ} → {X : Set} → {x : X} → {xs : Vec X m}    
    (p : m ≡ n) → subV (cong suc p) (x ∷ xs) ≡ x ∷ subV p xs 
subV∷ refl  = refl
-}

subV∷ : {m n : ℕ} → {X : Set} → {x : X} → {xs : Vec X m} → {ys : Vec X n} →    
    (p : m ≡ n) → subV p xs ≡ ys → subV (cong suc p) (x ∷ xs) ≡ x ∷ ys 
subV∷ refl refl = refl


ru++ : {n : ℕ} → {X : Set} → (xs : Vec X n) → subV lu (xs ++ []) ≡ xs
ru++ []       = refl
ru++ (x ∷ xs) = subV∷ lu (ru++ xs)
{-
  begin 
    subV (cong suc ru+) (x ∷ xs ++ []) 
  ≡⟨ subV∷ ru+ ⟩ 
    x ∷ subV ru+ (xs ++ [])
  ≡⟨ cong (_∷_ x) (ru++ xs) ⟩ 
    x ∷ xs 
  ∎
-}

mlaw1V : {n : ℕ} → {X Y : Set} → (f : X → Vec Y n) → (x : X) →
            subV lu (liftV f (ηV x)) ≡ f x
mlaw1V f x = ru++ (f x)


mlaw2V : {n : ℕ} → {X : Set} → (xs : Vec X n) →
            subV ru xs ≡ liftV ηV xs
mlaw2V []       = refl
mlaw2V (x ∷ xs) = subV∷ {x = x} {xs = xs} ru (mlaw2V xs) 


NDV : GradedMonad
NDV = record { OM = ℕ*
                 ; T = λ e X → Vec X e
                 ; η = ηV
                 ; lift = liftV 
                 ; sub = subV 
                 ; sub-mon = {!!}
                 ; sub-refl = {!!}
                 ; sub-trans = {!!}
                 ; mlaw1 = mlaw1V
                 ; mlaw2 = mlaw2V
                 ; mlaw3 = {!!}
                 }