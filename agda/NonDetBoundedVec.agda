module NonDetBoundedVec where

open import Function
--open import Data.List
open import Relation.Nullary


open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality hiding ([_]; inspect)

open import Finiteness
open import OrderedMonoid
open import GradedMonad

open import Data.Nat
open import Data.Vec

data BVec (X : Set) (n : ℕ) : Set where
  bv : {m : ℕ} → Vec X m →  m ≤ n → BVec X n

ℕ* : OrderedMonoid
ℕ* = record { M = ℕ
             ; _⊑_ = _≤_
             ; reflM = {!!}
             ; transM = {!!}
             ; i = 1
             ; _·_ = _*_
             ; mon = {!!}
             ; lu = {!!}
             ; ru = {!!} 
             ; ass = {!!}
             }

1≤1 : 1 ≤ 1
1≤1 = s≤s z≤n

≤+1 : {m n : ℕ} → m ≤ n → m ≤ suc n
≤+1 z≤n = z≤n
≤+1 (s≤s p) = s≤s (≤+1 p)

≤+ : {m m' n : ℕ} → m ≤ m' → m ≤ n + m'
≤+ {n = zero} p = p
≤+ {zero} {n = suc n} p = z≤n
≤+ {suc m} {zero} {suc n} ()
≤+ {suc m} {suc m'} {suc n} (s≤s p) = s≤s (≤+ {m} {suc m'} {n} (≤+1 p))

_+≤_ : {m m' n n' : ℕ} → m ≤ m' → n ≤ n' → m + n ≤ m' + n' 
_+≤_ {zero} {m'} {n} {n'} z≤n q = ≤+ {n} {n'} {m'} q
s≤s p +≤ q = s≤s (p +≤ q)


 
ηBV : {X : Set} → X → BVec X 1
ηBV x = bv (x ∷ []) 1≤1 

liftBV :  {m n : ℕ} {X Y : Set} →
        (X → BVec Y n) → BVec X m → BVec Y (m * n)
liftBV f (bv [] z≤n) = bv [] z≤n
liftBV f (bv (x ∷ xs) (s≤s p)) with f x | liftBV f (bv xs p)  
... | bv ys q | bv zs r = bv (ys ++ zs) (q +≤ r) 



NDBV : GradedMonad
NDBV = record    { OM = ℕ*
                 ; T = λ e X → BVec X e
                 ; η = ηBV
                 ; lift = λ {e} {e'} → liftBV {e} {e'}
                 ; sub = {!!}
                 ; sub-mon = {!!}
                 ; sub-refl = {!!}
                 ; sub-trans = {!!}
                 ; mlaw1 = {!!}
                 ; mlaw2 = {!!}
                 ; mlaw3 = {!!}
                 }

