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

≤+1 : {m n : ℕ} → m ≤ n → m ≤ suc n
≤+1 z≤n = z≤n
≤+1 (s≤s p) = s≤s (≤+1 p)

≤+ : (n : ℕ) {m m' : ℕ} → m ≤ m' → m ≤ n + m'
≤+ zero p = p
≤+ (suc n) z≤n = z≤n
≤+ (suc n) (s≤s p) = s≤s (≤+ n (≤+1 p))

mon+ : {m n m' n' : ℕ} → m ≤ m' → n ≤ n' → m + n ≤ m' + n'
mon+ {m' = m'} z≤n q = ≤+ m' q
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

+ass : {m n o : ℕ} → m + (n + o) ≡ (m + n) + o
+ass {zero} = refl
+ass {suc m} = cong suc (+ass {m})

dist+ : {m n o : ℕ} → (m + n) * o ≡ m * o + n * o
dist+ {zero}  {_} {_} = refl
dist+ {suc m} {n} {o} = trans (cong (_+_ o) (dist+ {m} {n} {o})) 
                              (+ass {o} {m * o} {n * o})

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


ηBV : {X : Set} → X → BVec X i
ηBV x = bv (x ∷ []) (s≤s z≤n)


liftBV :  {m n : ℕ} {X Y : Set} →
        (X → BVec Y n) → BVec X m → BVec Y (m · n)
liftBV f (bv [] z≤n) = bv [] z≤n
liftBV f (bv (x ∷ xs) (s≤s p)) = (f x) ++bv liftBV f (bv xs p)


subBV : {e e' : M} {X : Set} → e ⊑ e' → BVec X e → BVec X e'
subBV p (bv x q) = bv x (transM q p)




lemma-trans+1 : {m n o : ℕ} (p : m ≤ n) (q : o ≤ m) →
                ≤+1 (trans≤ q p) ≡ trans≤ q (≤+1 p)
lemma-trans+1 p z≤n = refl
lemma-trans+1 (s≤s p) (s≤s q) = cong s≤s (lemma-trans+1 p q)


lemma-≤+ : {m n o : ℕ} (x : ℕ) (p : m ≤ n) (q : o ≤ m) →
           transM q (≤+ x p) ≡ ≤+ x (transM q p)
lemma-≤+ zero p q = refl
lemma-≤+ (suc x) z≤n z≤n = refl
lemma-≤+ (suc x) (s≤s p) z≤n = refl
lemma-≤+ (suc x) (s≤s p) (s≤s q) rewrite lemma-trans+1 p q = cong s≤s (lemma-≤+ x (≤+1 p) q)

-- this is same as 'what'
wat : {m m' n n' o' : ℕ}
        (p : m ≤ n) (p' : m' ≤ n') (q' : o' ≤ m') →
        trans≤ (≤+ (suc m) (≤+1 (≤+1 q')))
        (s≤s (mon+ p (s≤s (s≤s p'))))
        ≡ ≤+ (suc n) (≤+1 (≤+1 (trans≤ q' p')))
wat p p' z≤n = refl
wat p (s≤s p') (s≤s q') = {!!}



-- this is same as 'lemma', but one step deeper
what :  {m m' n n' o' : ℕ}
        (p : m ≤ n) (p' : m' ≤ n') (q' : o' ≤ m') →
        trans≤ (≤+ (suc m) (≤+1 q')) (s≤s (mon+ p (s≤s p'))) ≡
        ≤+ (suc n) (≤+1 (trans≤ q' p'))
what p p' z≤n = refl
what {n = zero} z≤n (s≤s p') (s≤s z≤n) = refl
what {n = zero} z≤n (s≤s (s≤s p')) (s≤s (s≤s q')) = cong s≤s (what {n = zero} z≤n (s≤s p') (s≤s q'))
what {n = suc n} z≤n (s≤s p') (s≤s z≤n) = refl
what {n = suc n} z≤n (s≤s (s≤s p')) (s≤s (s≤s q')) rewrite lemma-trans+1 p' q' = cong s≤s (what {n = n} z≤n (s≤s (≤+1 p')) (s≤s q'))
what {suc m} {n = suc n} (s≤s p) (s≤s p') (s≤s q') = cong s≤s (wat p p' q')

lemma : {m m' n n' o' : ℕ}
        (p : m ≤ n) (p' : m' ≤ n') (q' : o' ≤ m') →
        trans≤ (≤+ m (≤+1 q')) (mon+ p (s≤s p')) ≡ ≤+ n (≤+1 (trans≤ q' p'))
lemma {n = zero} z≤n z≤n z≤n = refl
lemma {n = zero} z≤n (s≤s p') z≤n = refl
lemma {n = zero} z≤n (s≤s p') (s≤s q') = cong s≤s (lemma {n = zero} z≤n p' q')
lemma {n = suc n} z≤n p' z≤n = refl
lemma {n = suc n} z≤n (s≤s p') (s≤s q') rewrite lemma-trans+1 p' q' = cong s≤s (lemma {n = n} z≤n (≤+1 p') q')
lemma (s≤s p) p' q' = what p p' q'
--lemma (s≤s p) p' q' = {!!}


lemma-mon+ : {m m' n n' o o' : ℕ}
             (p : m ≤ n) (p' : m' ≤ n') (q : o ≤ m) (q' : o' ≤ m') →
             trans≤ (mon+ q q') (mon+ p p') ≡ mon+ (trans≤ q p) (trans≤ q' p')
lemma-mon+ {n = n} z≤n p' z≤n q' = lemma-≤+ n p' q'
lemma-mon+ (s≤s p) p' z≤n z≤n = refl
lemma-mon+ {suc m} {suc m'} {suc n} {suc n'} (s≤s p) (s≤s p') z≤n (s≤s q') = cong s≤s (lemma p p' q')
--lemma-mon+ {suc m} {suc m'} {suc n} {suc n'} (s≤s p) (s≤s p') z≤n (s≤s q') = {!!}
lemma-mon+ (s≤s p) p' (s≤s q) q' = cong s≤s (lemma-mon+ p p' q q')


lemma++ : {m m' n n' : ℕ} {X : Set} (p : m ≤ n) (p' : m' ≤ n')
          (xs : BVec X m) (xs' : BVec X m') →
          subBV (mon+ p p') (xs ++bv xs') ≡ subBV p xs ++bv subBV p' xs'
lemma++ p p' (bv xs q) (bv xs' q') = cong (bv (xs ++ xs'))
                                          (lemma-mon+ p p' q q')


subBV-mon : {e e' e'' e''' : M} {X Y : Set} (p : e ⊑ e'') (q : e' ⊑ e''')
      (f : X → BVec Y e') (c : BVec X e) →
      subBV (mon p q) (liftBV f c) ≡
      liftBV (λ x → subBV q (f x)) (subBV p c)
subBV-mon p q f (bv [] z≤n) = refl
subBV-mon {suc e} {e'} {suc e''} {e'''} (s≤s p) q f (bv (x ∷ xs) (s≤s r)) = 
  begin
    subBV (mon+ q (mon* p q)) (f x ++bv liftBV f (bv xs r))
  ≡⟨ lemma++ q (mon* p q) (f x) (liftBV f (bv xs r)) ⟩
    subBV q (f x) ++bv subBV (mon* p q) (liftBV f (bv xs r))
  ≡⟨ cong (_++bv_ (subBV q (f x))) (subBV-mon p q f (bv xs r)) ⟩
    subBV q (f x) ++bv
       liftBV (λ z → subBV q (f z)) (bv xs (trans≤ r p))
  ∎


transM-reflM : {e e' : M} (p : e ⊑ e') →
               transM p reflM ≡ p
transM-reflM z≤n = refl
transM-reflM (s≤s p) = cong s≤s (transM-reflM p)


subBV-refl : {e : M} {X : Set} (c : BVec X e) → subBV reflM c ≡ c
subBV-refl (bv xs p) = cong (bv xs) (transM-reflM p)


transM-ass : {e e' e'' e''' : M} (p : e ⊑ e') (q : e' ⊑ e'') (r : e'' ⊑ e''') →
            transM (transM p q) r ≡ transM p (transM q r)
transM-ass z≤n q r = refl
transM-ass (s≤s p) (s≤s q) (s≤s r) = cong s≤s (transM-ass p q r)


subBV-trans : {e e' e'' : M} {X : Set} (p : e ⊑ e') (q : e' ⊑ e'')
              (c : BVec X e) →
              subBV q (subBV p c) ≡ subBV (transM p q) c
subBV-trans p q (bv xs r) = cong (bv xs) (transM-ass r p q)


TBV = λ e X → BVec X e


subeq∷ : {m n : M} {X : Set} {x : X} {xs : BVec X m} {ys : BVec X n} →    
         (p : m ≡ n) → subeq {T = TBV} p xs ≡ ys →
         subeq {T = TBV} (cong suc p) (x ∷bv xs) ≡ x ∷bv ys
subeq∷ refl refl = refl


subeq-air : {m n o : M} {p : m ≤ n} {q : m ≤ o} (r : n ≡ o)
            {X : Set} (xs : Vec X m) →
            subeq {T = TBV} r (bv xs p) ≡ bv xs q
subeq-air {p = z≤n} {q = z≤n} refl [] = refl
subeq-air {p = s≤s p} {q = s≤s q} refl (x ∷ xs) = subeq∷ refl (subeq-air refl xs)


ru++ : {m n : M} {X : Set} (xs : Vec X m) (p : m ≤ n) →
       subeq {T = TBV} ru+ (bv (xs ++ []) (mon+ p z≤n)) ≡ bv xs p
ru++ [] (z≤n {n}) = subeq-air ru+ []
ru++ (x ∷ xs) (s≤s p) = subeq∷ ru+ (ru++ xs p)


blaw1 : {e : M} {X Y : Set} (f : X → BVec Y e) (x : X) →
        subeq {T = TBV} lu (liftBV f (ηBV x)) ≡ f x
blaw1 f x with f x
...       | bv xs p = ru++ xs p


head-bv : {X : Set} {n : ℕ} (x : X) (xs : BVec X n) →
          x ∷bv xs ≡ ηBV x ++bv xs
head-bv x (bv xs p) = refl


blaw2 : {e : M} {X : Set} (c : TBV e X) → subeq {T = TBV} ru c ≡ liftBV ηBV c
blaw2 (bv [] (z≤n {n})) = subeq-air (ru {n}) []
blaw2 (bv (x ∷ xs) (s≤s {m} {n} p)) = 
  begin
    subeq {T = TBV} ru (bv (x ∷ xs) (s≤s p))
  ≡⟨ refl ⟩
    subeq {T = TBV} ru (x ∷bv bv xs p)
  ≡⟨ subeq∷ {xs = bv xs p} ru refl ⟩
    x ∷bv (subeq {T = TBV} ru (bv xs p))
  ≡⟨ cong (_∷bv_ x) (blaw2 (bv xs p)) ⟩
    x ∷bv (liftBV ηBV (bv xs p))
  ≡⟨ head-bv x (liftBV ηBV (bv xs p)) ⟩
    ηBV x ++bv liftBV ηBV (bv xs p)
  ≡⟨ refl ⟩
    liftBV ηBV (bv (x ∷ xs) (s≤s p))
  ∎


subeq-lemma : {e e' : M} {X Y : Set} →
              (g : M → M) → (f : {e : M} → BVec X e → BVec Y (g e)) →
              (p : e ≡ e') → (xs : BVec X e) →
              subeq {T = TBV} (cong g p) (f xs) ≡ f (subeq {T = TBV} p xs)
subeq-lemma g f refl xs = refl

{-
≡2⊑ : {e e' : M} → e ≡ e' → e ⊑ e'
≡2⊑ {zero} p = z≤n
≡2⊑ {suc e} refl = s≤s (≡2⊑ refl)
-}

trans-ass : {e e' e'' e''' : M} (p : e ≡ e') (q : e' ≡ e'') (r : e'' ≡ e''') →
            trans (trans p q) r ≡ trans p (trans q r)
trans-ass refl q r = refl


subeq-trans : {e e' e'' : M} {X : Set} (p : e ≡ e') (q : e' ≡ e'')
              (c : BVec X e) →
              subeq {T = TBV} q (subeq {T = TBV} p c) ≡ subeq {T = TBV} (trans p q) c
subeq-trans refl q xs = refl


lemma-ass++ : {e e' e'' : M} {X : Set}
              (xs : BVec X e) (xs' : BVec X e') (xs'' : BVec X e'') →
              subeq {T = TBV} (+ass {e} {e'} {e''}) (xs ++bv (xs' ++bv xs''))
              ≡ (xs ++bv xs') ++bv xs''
lemma-ass++ (bv [] (z≤n {zero})) (bv xs' q) (bv xs'' r) = refl
lemma-ass++ {suc e} {e' = e'} {e''} (bv [] (z≤n)) (bv xs' q) (bv xs'' r) =
            subeq-air (cong suc (+ass {e} {e'} {e''}))
                      (xs' ++ xs'')
lemma-ass++ {suc e} {e'} {e''} (bv (x ∷ xs) (s≤s p)) (bv xs' q) (bv xs'' r) = subeq∷ (+ass {e} {e'} {e''}) (lemma-ass++ (bv xs p) (bv xs' q) (bv xs'' r))


lemma-z≤n : (e : M) {e' : M} → ≤+ e (z≤n {e'}) ≡ z≤n {e + e'}
lemma-z≤n zero = refl
lemma-z≤n (suc e) = refl

lemma-[] : (e : M) {e' : M} {X : Set} → bv {X} [] (≤+ e (z≤n {e'})) ≡ bv [] z≤n
lemma-[] e = cong (bv []) (lemma-z≤n e)


lemma-lift-[]++ : {e e' e'' : M} {X Y : Set}
                  (xs : BVec X e')
                  (f : X → BVec Y e'') →
                  liftBV f (bv [] (z≤n {suc e}) ++bv xs) ≡
                  (bv [] (z≤n {e''}) ++bv liftBV f (bv [] (z≤n {e}) ++bv xs))
lemma-lift-[]++ {zero} {e'} {e''} (bv [] z≤n) f = sym (lemma-[] e'')
lemma-lift-[]++ {zero} (bv (x ∷ xs) (s≤s p)) f = {!!}
lemma-lift-[]++ {suc e} {e'} {e''} (bv [] z≤n) f = sym (lemma-[] e'')
lemma-lift-[]++ {suc e} (bv (x ∷ xs) (s≤s p)) f = {!!}


lemma-dist : {e e' e'' : M} {X Y : Set}
             (xs : BVec X e)
             (xs' : BVec X e')
             (f : X → BVec Y e'') →
             subeq {T = TBV} (dist+ {e} {e'} {e''}) (liftBV f (xs ++bv xs'))
             ≡ liftBV f xs ++bv liftBV f xs'
lemma-dist {zero} (bv [] z≤n) (bv xs' q) f with liftBV f (bv xs' q)
...                                        | bv ys r = refl
lemma-dist {suc e} {e'} {e''} (bv [] z≤n) (bv [] z≤n) f =
           subeq-air (trans (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                            (+ass {e''} {e · e''} {e' · e''})) []
lemma-dist {suc e} {e'} {e''} (bv [] z≤n) xs' f = 
  begin
    subeq (trans (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                 (+ass {e''} {e · e''} {e' · e''}))
          (liftBV f (bv [] (z≤n {suc e}) ++bv xs'))
  ≡⟨ cong (subeq (trans (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                        (+ass {e''} {_·_ e e''} {_·_ e' e''})))
          (lemma-lift-[]++ xs' f) ⟩
    subeq (trans (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                 (+ass {e''} {e · e''} {e' · e''}))
          (bv [] (z≤n {e''}) ++bv liftBV f (bv [] (z≤n {e}) ++bv xs'))
  ≡⟨ sym (subeq-trans (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                      (+ass {e''} {e · e''} {e' · e''}) _) ⟩
    subeq (+ass {e''} {e · e''} {e' · e''})
          (subeq {T = TBV} (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                 (bv [] (z≤n {e''}) ++bv liftBV f (bv [] (z≤n {e}) ++bv xs')))
  ≡⟨ cong (subeq {T = TBV} (+ass {e''} {e · e''} {e' · e''}))
          (subeq-lemma (_+_ e'') (_++bv_ (bv [] (z≤n {e''}))) (dist+ {e} {e'} {e''})
                       (liftBV f (bv [] (z≤n {e}) ++bv xs'))) ⟩
    subeq (+ass {e''} {e · e''} {e' · e''})
      (bv [] (z≤n {e''}) ++bv subeq {T = TBV} (dist+ {e} {e'} {e''})
                                    (liftBV f (bv [] (z≤n {e}) ++bv xs')))
  ≡⟨ cong (λ ys → subeq {T = TBV} (+ass {e''} {e · e''} {e' · e''})
                         (bv [] (z≤n {e''}) ++bv ys))
          (lemma-dist (bv [] (z≤n {e})) xs' f) ⟩
    subeq ((+ass {e''} {e · e''} {e' · e''}))
          (bv [] (z≤n {e''}) ++bv (bv [] (z≤n {e · e''}) ++bv liftBV f xs'))
  ≡⟨ lemma-ass++ (bv [] (z≤n {e''})) (bv [] (z≤n {e · e''})) (liftBV f xs') ⟩
    (bv [] (z≤n {e''}) ++bv bv [] (z≤n {e · e''})) ++bv liftBV f xs'
  ≡⟨ cong (λ xs → xs ++bv liftBV f xs') (lemma-[] e'') ⟩
    bv [] (z≤n {suc e · e''}) ++bv liftBV f xs'
  ∎
lemma-dist {suc e} {e'} {e''} (bv (x ∷ xs) (s≤s p)) (bv xs' p') f =
  begin
    subeq {T = TBV} (dist+ {suc e} {e'} {e''})
          (liftBV f (bv (x ∷ xs ++ xs') (mon+ (s≤s p) p')))
  ≡⟨ refl ⟩
    subeq {T = TBV} (dist+ {suc e} {e'} {e''})
          (f x ++bv liftBV f (bv (xs ++ xs') (mon+ p p')))
  ≡⟨ sym (subeq-trans (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                      (+ass {e''} {e · e''} {e' · e''}) _) ⟩
    subeq {T = TBV} (+ass {e''} {e · e''} {e' · e''})
          (subeq {T = TBV} (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                 (f x ++bv liftBV f (bv (xs ++ xs') (mon+ p p'))))
  ≡⟨ cong (subeq {T = TBV} (+ass {e''} {e · e''} {e' · e''}))
          (subeq-lemma (_+_ e'') (_++bv_ (f x)) (dist+ {e} {e'} {e''})
                       (liftBV f (bv (xs ++ xs') (mon+ p p')))) ⟩
    subeq {T = TBV} (+ass {e''} {e · e''} {e' · e''})
          (f x ++bv subeq {T = TBV} (dist+ {e} {e'} {e''})
                          (liftBV f (bv (xs ++ xs') (mon+ p p'))))
  ≡⟨ cong (λ ys → subeq {T = TBV} (+ass {e''} {e · e''} {e' · e''}) (f x ++bv ys))
          (lemma-dist {e} {e'} {e''} (bv xs p) (bv xs' p') f) ⟩
    subeq {T = TBV} (+ass {e''} {e · e''} {e' · e''})
          (f x ++bv (liftBV f (bv xs p) ++bv liftBV f (bv xs' p')))
  ≡⟨ lemma-ass++ (f x) (liftBV f (bv xs p)) (liftBV f (bv xs' p')) ⟩
    (f x ++bv liftBV f (bv xs p)) ++bv liftBV f (bv xs' p')
  ≡⟨ refl ⟩
    liftBV f (bv (x ∷ xs) (s≤s p)) ++bv liftBV f (bv xs' p')
  ∎


blaw3 : {e e' e'' : M} {X Y Z : Set} (f : X → TBV e' Y)
        (g : Y → TBV e'' Z) (c : TBV e X) →
        subeq {T = TBV} (ass {e} {e'} {e''}) (liftBV g (liftBV f c)) ≡
        liftBV (λ x → liftBV g (f x)) c
blaw3 {e} {e'} {e''} f g (bv [] z≤n) = subeq-air (ass {e} {e'} {e''}) []
blaw3 {suc e} {e'} {e''} f g (bv (x ∷ xs) (s≤s p)) = 
  begin
    subeq {T = TBV} (ass {suc e} {e'} {e''}) (liftBV g (liftBV f (bv (x ∷ xs) (s≤s p))))
  ≡⟨ refl ⟩
    subeq {T = TBV} (ass {suc e} {e'} {e''}) (liftBV g (liftBV f (x ∷bv (bv xs p))))
  ≡⟨ refl ⟩
    subeq {T = TBV} (ass {suc e} {e'} {e''}) (liftBV g (f x ++bv liftBV f (bv xs p)))
  ≡⟨ sym (subeq-trans (dist+ {e'} {e · e'} {e''})
                      (cong (_+_ (e' · e'')) (ass {e} {e'} {e''})) _) ⟩
    subeq {T = TBV} (cong (_+_ (e' · e'')) (ass {e} {e'} {e''}))
                    (subeq {T = TBV} (dist+ {e'} {e · e'} {e''})
                           (liftBV g (f x ++bv liftBV f (bv xs p))))
  ≡⟨ cong (subeq {T = TBV} (cong (_+_ (e' · e'')) (ass {e} {e'} {e''})))
                 (lemma-dist (f x) (liftBV f (bv xs p)) g) ⟩
    subeq {T = TBV} (cong (_+_ (e' · e'')) (ass {e} {e'} {e''}))
          (liftBV g (f x) ++bv liftBV g (liftBV f (bv xs p)))
  ≡⟨ subeq-lemma (_+_ (e' · e'')) (_++bv_ (liftBV g (f x))) (ass {e} {e'} {e''}) _ ⟩
    liftBV g (f x) ++bv subeq {T = TBV} (ass {e} {e'} {e''})
                                        (liftBV g (liftBV f (bv xs p)))
  ≡⟨ cong (_++bv_ (liftBV g (f x))) (blaw3 f g (bv xs p)) ⟩
    liftBV g (f x) ++bv liftBV (λ x → liftBV g (f x)) (bv xs p)
  ≡⟨ refl ⟩
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

