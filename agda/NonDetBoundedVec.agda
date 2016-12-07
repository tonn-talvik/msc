module NonDetBoundedVec where

open import Function
--open import Data.List
open import Relation.Nullary


open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality hiding ([_]; inspect)
open ≡-Reasoning

open import Finiteness
open import OrderedMonoid
open import GradedMonad

open import Data.Nat
open import Data.Vec

data BVec (X : Set) (n : ℕ) : Set where
  bv : {m : ℕ} → Vec X m →  m ≤ n → BVec X n

refl≤ : {m : ℕ} → m ≤ m
refl≤ {zero} = z≤n
refl≤ {suc m} = s≤s refl≤

trans≤ : {m n o : ℕ} → m ≤ n → n ≤ o → m ≤ o
trans≤ z≤n q = z≤n
trans≤ (s≤s p) (s≤s q) = s≤s (trans≤ p q)

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


mon+ : {m n m' n' : ℕ} → m ≤ m' → n ≤ n' → m + n ≤ m' + n'
mon+ = _+≤_

mon* : {m n m' n' : ℕ} → m ≤ m' → n ≤ n' → m * n ≤ m' * n'
mon* z≤n q = z≤n
mon* (s≤s p) q = mon+ q (mon* p q)

ru+ : {m : ℕ} → m + zero ≡ m
ru+ {zero} = refl
ru+ {suc m} = cong suc ru+

lu* : {n : ℕ} → 1 * n ≡ n
lu* = ru+ 

ru* : {m : ℕ} → m ≡ m * 1
ru* {zero} = refl
ru* {suc m} = cong suc ru*

ass+ : {m n o : ℕ} → (m + n) + o ≡ m + (n + o)
ass+ {zero} = refl
ass+ {suc m} = cong suc (ass+ {m})

dist+ : {m n o : ℕ} → (m + n) * o ≡ m * o + n * o
dist+ {zero}  {_} {_} = refl
dist+ {suc m} {n} {o} = trans (cong (_+_ o) (dist+ {m} {n} {o})) 
                              (sym (ass+ {o} {m * o} {n * o}))

ass* : {m n o : ℕ} → m * n * o ≡ m * (n * o)
ass* {zero} = refl
ass* {suc m} {n} {o} = begin
                  (n + m * n) * o
                ≡⟨ dist+ {n} {m * n} {o}  ⟩
                  n * o + (m * n) * o
                ≡⟨ cong (λ x → n * o + x) (ass* {m} {n} {o}) ⟩
                  n * o + m * (n * o)
                ∎

ℕ* : OrderedMonoid
ℕ* = record { M = ℕ
             ; _⊑_ = _≤_
             ; reflM = refl≤
             ; transM = trans≤
             ; i = 1
             ; _·_ = _*_
             ; mon = mon*
             ; lu = lu*
             ; ru = ru*
             ; ass = λ {m n o} → ass* {m} {n} {o}
             }

open OrderedMonoid.OrderedMonoid ℕ*
 
ηBV : {X : Set} → X → BVec X 1
ηBV x = bv (x ∷ []) 1≤1 

liftBV :  {m n : ℕ} {X Y : Set} →
        (X → BVec Y n) → BVec X m → BVec Y (m * n)
liftBV f (bv [] z≤n) = bv [] z≤n
liftBV f (bv (x ∷ xs) (s≤s p)) with f x | liftBV f (bv xs p)  
... | bv ys q | bv zs r = bv (ys ++ zs) (q +≤ r) 

subBV : {e e' : M} {X : Set} → e ⊑ e' → BVec X e → BVec X e'
subBV p (bv x q) = bv x (trans≤ q p)

subBV-mon : {e e' e'' e''' : M} {X Y : Set} (p : e ⊑ e'') (q : e' ⊑ e''')
      (f : X → BVec Y e') (c : BVec X e) →
      subBV (mon p q) (liftBV f c) ≡
      liftBV (λ x → subBV q (f x)) (subBV p c)
subBV-mon p q f (bv x r) = {!!}

NDBV : GradedMonad
NDBV = record    { OM = ℕ*
                 ; T = λ e X → BVec X e
                 ; η = ηBV
                 ; lift = λ {e} {e'} → liftBV {e} {e'}
                 ; sub = subBV
                 ; sub-mon = subBV-mon
                 ; sub-refl = {!!}
                 ; sub-trans = {!!}
                 ; mlaw1 = {!!}
                 ; mlaw2 = {!!}
                 ; mlaw3 = {!!}
                 }

