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

mon+ : {m n m' n' : ℕ} → m ≤ m' → n ≤ n' → m + n ≤ m' + n'
mon+ {zero} {n} {m'} {n'} z≤n q = ≤+ {n} {n'} {m'} q
mon+ (s≤s p) q = s≤s (mon+ p q)

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
ass* {suc m} {n} {o} = trans (dist+ {n} {m * n} {o})
                             (cong (_+_ (n * o)) (ass* {m} {n} {o}))

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


data BVec (X : Set) : (n : ℕ) → Set where
  bv : {m n : ℕ} → Vec X m →  m ≤ n → BVec X n

_∷bv_ : {X : Set} {n : ℕ} → X → BVec X n → BVec X (suc n)
x ∷bv (bv xs p) = bv (x ∷ xs) (s≤s p)

_++bv_ : {X : Set} {m n : ℕ} → BVec X m → BVec X n → BVec X (m + n)
bv xs p ++bv bv xs' q = bv (xs ++ xs') (mon+ p q)

ruu : {m : M} → m ≡ m * i
ruu {zero} = refl
ruu {suc m} = cong suc ruu

ηBV : {X : Set} → X → BVec X i
ηBV x = bv (x ∷ []) 1≤1 


liftBV :  {m n : ℕ} {X Y : Set} →
        (X → BVec Y n) → BVec X m → BVec Y (m · n)
liftBV f (bv [] z≤n) = bv [] z≤n
liftBV f (bv (x ∷ xs) (s≤s p)) = (f x) ++bv liftBV f (bv xs p)
--liftBV f (bv (x ∷ xs) (s≤s p)) with f x | liftBV f (bv xs p)  
--... | bv ys q | bv zs r = bv (ys ++ zs) (mon+ q r) 


subBV : {e e' : M} {X : Set} → e ⊑ e' → BVec X e → BVec X e'
subBV p (bv x q) = bv x (transM q p)


subBV-mon : {e e' e'' e''' : M} {X Y : Set} (p : e ⊑ e'') (q : e' ⊑ e''')
      (f : X → BVec Y e') (c : BVec X e) →
      subBV (mon p q) (liftBV f c) ≡
      liftBV (λ x → subBV q (f x)) (subBV p c)
subBV-mon p q f (bv [] z≤n) = refl
subBV-mon {suc e} {e'} {suc e''} {e'''} (s≤s p) q f (bv (x ∷ xs) (s≤s r)) = 
  begin
    subBV (mon+ q (mon* p q)) (f x ++bv liftBV f (bv xs r))
  ≡⟨ {!!} ⟩
    subBV (mon+ q refl≤) (f x ++bv subBV (mon* p q) (liftBV f (bv xs r)))
  ≡⟨ {!!} ⟩
    subBV q (f x) ++bv
       liftBV (λ z → subBV q (f z)) (bv xs (trans≤ r p))
  ∎
{-subBV-mon (s≤s p) q f (bv (x ∷ xs) (s≤s r)) = 
  begin
    subBV (mon (s≤s p) q) (liftBV f (bv (x ∷ xs) (s≤s r)))
  ≡⟨ {!!} ⟩
    liftBV (λ x → subBV q (f x)) (x ∷bv subBV p (bv xs r))
  ≡⟨ refl ⟩
    liftBV (λ x → subBV q (f x)) (subBV (s≤s p) (bv (x ∷ xs) (s≤s r)))
  ∎-}


transM-reflM : {e e' : M} (p : e ⊑ e') →
               transM p reflM ≡ p
transM-reflM z≤n = refl
transM-reflM (s≤s p) = cong s≤s (transM-reflM p)


subBV-refl : {e : M} {X : Set} (c : BVec X e) → subBV reflM c ≡ c
subBV-refl (bv x p) = cong (bv x) (transM-reflM p)


trans-ass : {e e' e'' e''' : M} (p : e ⊑ e') (q : e' ⊑ e'') (r : e'' ⊑ e''') →
            transM (transM p q) r ≡ transM p (transM q r)
trans-ass z≤n q r = refl
trans-ass (s≤s p) (s≤s q) (s≤s r) = cong s≤s (trans-ass p q r)

subBV-trans : {e e' e'' : M} {X : Set} (p : e ⊑ e') (q : e' ⊑ e'')
              (c : BVec X e) →
              subBV q (subBV p c) ≡ subBV (transM p q) c
subBV-trans p q (bv x r) = cong (bv x) (trans-ass r p q)

TBV = λ e X → BVec X e


subeq∷ : {m n : M} {X : Set} {x : X} {xs : BVec X m} {ys : BVec X n} →    
        (p : m ≡ n) → subeq {T = TBV} p xs ≡ ys → subeq {T = TBV} (cong suc p) (x ∷bv xs) ≡ x ∷bv ys
subeq∷ refl refl = refl


subeq-air : {n n' : M} (p : n ≡ n') {X : Set} →
            subeq {T = TBV} {X = X} p (bv [] (z≤n {n})) ≡ bv [] (z≤n {n'})
subeq-air refl = refl


ru++ : {m n : M} {X : Set} (xs : Vec X m) (p : m ≤ n) →
       subeq {T = TBV} ru+ (bv (xs ++ []) (mon+ p z≤n)) ≡ bv xs p
ru++ [] (z≤n {zero}) = refl
ru++ [] (z≤n {suc n}) = subeq-air ru+
ru++ (x ∷ xs) (s≤s p) = subeq∷ ru+ (ru++ xs p)


blaw1 : {e : M} {X Y : Set} (f : X → BVec Y e) (x : X) →
        subeq {T = TBV} lu (liftBV f (ηBV x)) ≡ f x
blaw1 f x with f x
...       | bv xs p = ru++ xs p


blaw2 : {e : M} {X : Set} (c : TBV e X) → subeq {T = TBV} ru c ≡ liftBV ηBV c
blaw2 (bv [] (z≤n {n})) = subeq-air (ru {n})
blaw2 (bv (x ∷ xs) (s≤s {m} {n} p)) = 
  begin
    subeq {T = TBV} ru (bv (x ∷ xs) (s≤s p))
  ≡⟨ refl ⟩
    subeq {T = TBV} ru (x ∷bv bv xs p)
  ≡⟨ subeq∷ {xs = bv xs p} ru refl ⟩
    x ∷bv (subeq {T = TBV} ru (bv xs p))
  ≡⟨ cong (_∷bv_ x) (blaw2 (bv xs p)) ⟩
    x ∷bv (liftBV ηBV (bv xs p))
  ≡⟨ {!!} ⟩
    liftBV ηBV (bv (x ∷ xs) (s≤s p))
  ∎


blaw3 : {e e' e'' : M} {X Y Z : Set} (f : X → TBV e' Y)
        (g : Y → TBV e'' Z) (c : TBV e X) →
        subeq {T = TBV} (ass {e} {e'} {e''}) (liftBV g (liftBV f c)) ≡
        liftBV (λ x → liftBV g (f x)) c
blaw3 {e} {e'} {e''} f g (bv [] z≤n) = subeq-air (ass {e} {e'} {e''})
blaw3 {suc e} {e'} {e''} f g (bv (x ∷ xs) (s≤s p)) = 
  begin
    subeq {T = TBV} (ass {suc e} {e'} {e''}) (liftBV g (liftBV f (bv (x ∷ xs) (s≤s p))))
  ≡⟨ refl ⟩
    subeq {T = TBV} (ass {suc e} {e'} {e''}) (liftBV g (liftBV f (x ∷bv (bv xs p))))
  ≡⟨ {!!} ⟩
    liftBV (λ x → liftBV g (f x)) (bv (x ∷ xs) (s≤s p))
  ∎

NDBV : GradedMonad
NDBV = record    { OM = ℕ*
                 ; T = TBV
                 ; η = ηBV
                 ; lift = λ {e} {e'} → liftBV {e} {e'}
                 ; sub = subBV
                 ; sub-mon = subBV-mon
                 ; sub-refl = subBV-refl
                 ; sub-trans = subBV-trans
                 ; mlaw1 = blaw1
                 ; mlaw2 = blaw2
                 ; mlaw3 = blaw3
                 }

