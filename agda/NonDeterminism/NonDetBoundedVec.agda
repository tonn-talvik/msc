module NonDetBoundedVec where

open import Data.Nat
open import Data.Vec
open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality hiding ([_]; inspect)
open ≡-Reasoning

open import Finiteness
open import Grading

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
ℕ* = record { E = ℕ
            ; _·_ = _*_
            ; i = 1
            ; lu = lu*
            ; ru = ru*
            ; ass = λ {m n o} → ass* {m} {n} {o}
            ; _⊑_ = _≤_
            ; ⊑-refl = refl≤
            ; ⊑-trans = trans≤
            ; mon = mon*
            }

open Grading.OrderedMonoid ℕ*


data BVec (X : Set) : (n : ℕ) → Set where
  bv : {m n : ℕ} → Vec X m → m ≤ n → BVec X n


_∷bv_ : {X : Set} {n : ℕ} → X → BVec X n → BVec X (suc n)
x ∷bv (bv xs p) = bv (x ∷ xs) (s≤s p)


_++bv_ : {X : Set} {m n : ℕ} → BVec X m → BVec X n → BVec X (m + n)
bv xs p ++bv bv xs' q = bv (xs ++ xs') (mon+ p q)



ηBV : {X : Set} → X → BVec X i
ηBV x = bv (x ∷ []) (s≤s z≤n)


bindBV :  {m n : ℕ} {X Y : Set} →
        (X → BVec Y n) → BVec X m → BVec Y (m · n)
bindBV f (bv [] z≤n) = bv [] z≤n
bindBV f (bv (x ∷ xs) (s≤s p)) = (f x) ++bv bindBV f (bv xs p)


subBV : {e e' : E} {X : Set} → e ⊑ e' → BVec X e → BVec X e'
subBV p (bv x q) = bv x (⊑-trans q p)


ans : {n n' : ℕ} → (p p' : n ≤ n') → p ≡ p'
ans z≤n z≤n = refl
ans (s≤s p) (s≤s p') = cong s≤s (ans p p')




lemma++ : {m m' n n' : ℕ} {X : Set} (p : m ≤ n) (p' : m' ≤ n')
          (xs : BVec X m) (xs' : BVec X m') →
          subBV (mon+ p p') (xs ++bv xs') ≡ subBV p xs ++bv subBV p' xs'
lemma++ p p' (bv xs q) (bv xs' q') = cong (bv (xs ++ xs'))
                                          (ans (trans≤ (mon+ q q') (mon+ p p')) (mon+ (trans≤ q p) (trans≤ q' p')))


subBV-mon : {e e' e'' e''' : E} {X Y : Set} (p : e ⊑ e'') (q : e' ⊑ e''')
      (f : X → BVec Y e') (c : BVec X e) →
      subBV (mon p q) (bindBV f c) ≡
      bindBV (λ x → subBV q (f x)) (subBV p c)
subBV-mon p q f (bv [] z≤n) = refl
subBV-mon {suc e} {e'} {suc e''} {e'''} (s≤s p) q f (bv (x ∷ xs) (s≤s r)) = 
  begin
    subBV (mon+ q (mon* p q)) (f x ++bv bindBV f (bv xs r))
  ≡⟨ lemma++ q (mon* p q) (f x) (bindBV f (bv xs r)) ⟩
    subBV q (f x) ++bv subBV (mon* p q) (bindBV f (bv xs r))
  ≡⟨ cong (_++bv_ (subBV q (f x))) (subBV-mon p q f (bv xs r)) ⟩
    subBV q (f x) ++bv
       bindBV (λ z → subBV q (f z)) (bv xs (trans≤ r p))
  ∎





⊑-trans-⊑-refl : {e e' : E} (p : e ⊑ e') →
               ⊑-trans p ⊑-refl ≡ p
⊑-trans-⊑-refl z≤n = refl
⊑-trans-⊑-refl (s≤s p) = cong s≤s (⊑-trans-⊑-refl p)


subBV-refl : {e : E} {X : Set} (c : BVec X e) → subBV ⊑-refl c ≡ c
subBV-refl (bv xs p) = cong (bv xs) (⊑-trans-⊑-refl p)



subBV-mon1 : {e e' e'' : E} {X Y : Set} (p : e ⊑ e'') 
      (f : X → BVec Y e') (c : BVec X e) →
      subBV (mon* p refl≤) (bindBV f c) ≡
      bindBV f (subBV p c)
subBV-mon1 p f (bv [] z≤n) = refl
subBV-mon1 {suc e} {e'} {suc e''} (s≤s p) f (bv (x ∷ xs) (s≤s r)) = let q = refl≤ {e'} in 
  begin
    subBV (mon+ q (mon* p q)) (f x ++bv bindBV f (bv xs r))
  ≡⟨ lemma++ q (mon* p q) (f x) (bindBV f (bv xs r)) ⟩
    subBV q (f x) ++bv subBV (mon* p q) (bindBV f (bv xs r))
  ≡⟨ cong (_++bv_ (subBV q (f x))) (subBV-mon1 p f (bv xs r)) ⟩
    subBV q (f x) ++bv
       bindBV f (bv xs (trans≤ r p))
   ≡⟨ cong₂ _++bv_ (subBV-refl (f x)) refl ⟩
    f x ++bv
       bindBV f (bv xs (trans≤ r p))
  ∎



⊑-trans-ass : {e e' e'' e''' : E} (p : e ⊑ e') (q : e' ⊑ e'') (r : e'' ⊑ e''') →
            ⊑-trans (⊑-trans p q) r ≡ ⊑-trans p (⊑-trans q r)
⊑-trans-ass z≤n q r = refl
⊑-trans-ass (s≤s p) (s≤s q) (s≤s r) = cong s≤s (⊑-trans-ass p q r)


subBV-trans : {e e' e'' : E} {X : Set} (p : e ⊑ e') (q : e' ⊑ e'')
              (c : BVec X e) →
              subBV q (subBV p c) ≡ subBV (⊑-trans p q) c
subBV-trans p q (bv xs r) = cong (bv xs) (⊑-trans-ass r p q)


TBV = λ e X → BVec X e


subeq∷ : {m n : E} {X : Set} {x : X} {xs : BVec X m} {ys : BVec X n} →    
         (p : m ≡ n) → subeq {T = TBV} p xs ≡ ys →
         subeq {T = TBV} (cong suc p) (x ∷bv xs) ≡ x ∷bv ys
subeq∷ refl refl = refl


subeq-air : {m n o : E} {p : m ≤ n} {q : m ≤ o} (r : n ≡ o)
            {X : Set} (xs : Vec X m) →
            subeq {T = TBV} r (bv xs p) ≡ bv xs q
subeq-air {p = z≤n} {q = z≤n} refl [] = refl
subeq-air {p = s≤s p} {q = s≤s q} refl (x ∷ xs) = subeq∷ refl (subeq-air refl xs)


ru++ : {m n : E} {X : Set} (xs : Vec X m) (p : m ≤ n) →
       subeq {T = TBV} ru+ (bv (xs ++ []) (mon+ p z≤n)) ≡ bv xs p
ru++ [] (z≤n {n}) = subeq-air ru+ []
ru++ (x ∷ xs) (s≤s p) = subeq∷ ru+ (ru++ xs p)


mlaw1BV : {e : E} {X Y : Set} (f : X → BVec Y e) (x : X) →
        subeq {T = TBV} lu (bindBV f (ηBV x)) ≡ f x
mlaw1BV f x with f x
...       | bv xs p = ru++ xs p


head-bv : {X : Set} {n : ℕ} (x : X) (xs : BVec X n) →
          x ∷bv xs ≡ ηBV x ++bv xs
head-bv x (bv xs p) = refl


mlaw2BV : {e : E} {X : Set} (c : TBV e X) → subeq {T = TBV} ru c ≡ bindBV ηBV c
mlaw2BV (bv [] (z≤n {n})) = subeq-air (ru {n}) []
mlaw2BV (bv (x ∷ xs) (s≤s {m} {n} p)) = 
  begin
    subeq {T = TBV} ru (bv (x ∷ xs) (s≤s p))
  ≡⟨ refl ⟩
    subeq {T = TBV} ru (x ∷bv bv xs p)
  ≡⟨ subeq∷ {xs = bv xs p} ru refl ⟩
    x ∷bv (subeq {T = TBV} ru (bv xs p))
  ≡⟨ cong (_∷bv_ x) (mlaw2BV (bv xs p)) ⟩
    x ∷bv (bindBV ηBV (bv xs p))
  ≡⟨ head-bv x (bindBV ηBV (bv xs p)) ⟩
    ηBV x ++bv bindBV ηBV (bv xs p)
  ≡⟨ refl ⟩
    bindBV ηBV (bv (x ∷ xs) (s≤s p))
  ∎


subeq-lemma : {e e' : E} {X Y : Set} →
              (g : E → E) → (f : {e : E} → BVec X e → BVec Y (g e)) →
              (p : e ≡ e') → (xs : BVec X e) →
              subeq {T = TBV} (cong g p) (f xs) ≡ f (subeq {T = TBV} p xs)
subeq-lemma g f refl xs = refl



subeq-trans : {e e' e'' : E} {X : Set} (p : e ≡ e') (q : e' ≡ e'')
              (c : BVec X e) →
              subeq {T = TBV} q (subeq {T = TBV} p c) ≡ subeq {T = TBV} (trans p q) c
subeq-trans refl q xs = refl


lemma-ass++ : {e e' e'' : E} {X : Set}
              (xs : BVec X e) (xs' : BVec X e') (xs'' : BVec X e'') →
              subeq {T = TBV} (+ass {e} {e'} {e''}) (xs ++bv (xs' ++bv xs''))
              ≡ (xs ++bv xs') ++bv xs''
lemma-ass++ (bv [] (z≤n {zero})) (bv xs' q) (bv xs'' r) = refl
lemma-ass++ {suc e} {e' = e'} {e''} (bv [] (z≤n)) (bv xs' q) (bv xs'' r) =
            subeq-air (cong suc (+ass {e} {e'} {e''}))
                      (xs' ++ xs'')
lemma-ass++ {suc e} {e'} {e''} (bv (x ∷ xs) (s≤s p)) (bv xs' q) (bv xs'' r) = subeq∷ (+ass {e} {e'} {e''}) (lemma-ass++ (bv xs p) (bv xs' q) (bv xs'' r))


lemma-z≤n : (e : E) {e' : E} → ≤+ e (z≤n {e'}) ≡ z≤n {e + e'}
lemma-z≤n zero = refl
lemma-z≤n (suc e) = refl

lemma-[] : (e : E) {e' : E} {X : Set} → bv {X} [] (≤+ e (z≤n {e'})) ≡ bv [] z≤n
lemma-[] e = cong (bv []) (lemma-z≤n e)

lemma'-[] : {X : Set} {e e' : E} (p : zero ≤ e) (xs : BVec X e') → bv [] p ++bv xs ≡ subBV (mon+ p refl≤) xs 
lemma'-[] p (bv xs q) = cong (bv xs) (ans (mon+ p q) (trans≤ q (mon+ p refl≤)))


lemma-bind-[]++ : {e e' e'' : E} {X Y : Set}
                  (xs : BVec X e')
                  (f : X → BVec Y e'') →
                  bindBV f (bv [] (z≤n {suc e}) ++bv xs) ≡
                  (bv [] (z≤n {e''}) ++bv bindBV f (bv [] (z≤n {e}) ++bv xs))

lemma-bind-[]++ {e} {e'} {e''} xs f = 
    let 
      p = mon+ (z≤n {e}) (refl≤ {e'})
      q = ≤+1 (refl≤ {e + e'})
    in
    begin
      bindBV f (bv [] (z≤n {suc e}) ++bv xs) 
    ≡⟨ cong (bindBV f) (lemma'-[] (z≤n {suc e}) xs)   ⟩
      bindBV f (subBV (mon+ (z≤n {suc e}) (refl≤ {e'})) xs) 
    ≡⟨ cong (λ p → bindBV f (subBV p xs)) (ans _ (trans≤ p q)) ⟩
     bindBV f (subBV (trans≤ p q) xs)
    ≡⟨  cong (bindBV f) (sym (subBV-trans p q xs))  ⟩
     bindBV f (subBV q (subBV p xs))
    ≡⟨  sym (subBV-mon1 q f (subBV p xs))  ⟩
     subBV (mon* q (refl≤ {e''})) (bindBV f (subBV p xs))
    ≡⟨  cong (λ p' → subBV p' (bindBV f (subBV p xs))) (ans _ _) ⟩
     subBV (mon+ (z≤n {e''}) (refl≤ {(e + e') * e''})) (bindBV f (subBV p xs))
    ≡⟨  sym (lemma'-[]  (z≤n {e''}) _) ⟩
      bv [] (z≤n {e''}) ++bv bindBV f (subBV p xs) 
    ≡⟨  cong (λ ys → bv []  (z≤n {e''}) ++bv bindBV f ys) (sym (lemma'-[] (z≤n {e}) xs))  ⟩                 
      bv [] (z≤n {e''}) ++bv bindBV f (bv [] (z≤n {e}) ++bv xs)
    ∎ 


lemma-dist : {e e' e'' : E} {X Y : Set}
             (xs : BVec X e)
             (xs' : BVec X e')
             (f : X → BVec Y e'') →
             subeq {T = TBV} (dist+ {e} {e'} {e''}) (bindBV f (xs ++bv xs'))
             ≡ bindBV f xs ++bv bindBV f xs'
lemma-dist {zero} (bv [] z≤n) (bv xs' q) f with bindBV f (bv xs' q)
...                                        | bv ys r = refl
lemma-dist {suc e} {e'} {e''} (bv [] z≤n) (bv [] z≤n) f =
           subeq-air (trans (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                            (+ass {e''} {e · e''} {e' · e''})) []
lemma-dist {suc e} {e'} {e''} (bv [] z≤n) xs' f = 
  begin
    subeq (trans (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                 (+ass {e''} {e · e''} {e' · e''}))
          (bindBV f (bv [] (z≤n {suc e}) ++bv xs'))
  ≡⟨ cong (subeq (trans (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                        (+ass {e''} {_·_ e e''} {_·_ e' e''})))
          (lemma-bind-[]++ xs' f) ⟩
    subeq (trans (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                 (+ass {e''} {e · e''} {e' · e''}))
          (bv [] (z≤n {e''}) ++bv bindBV f (bv [] (z≤n {e}) ++bv xs'))
  ≡⟨ sym (subeq-trans (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                      (+ass {e''} {e · e''} {e' · e''}) _) ⟩
    subeq (+ass {e''} {e · e''} {e' · e''})
          (subeq {T = TBV} (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                 (bv [] (z≤n {e''}) ++bv bindBV f (bv [] (z≤n {e}) ++bv xs')))
  ≡⟨ cong (subeq {T = TBV} (+ass {e''} {e · e''} {e' · e''}))
          (subeq-lemma (_+_ e'') (_++bv_ (bv [] (z≤n {e''}))) (dist+ {e} {e'} {e''})
                       (bindBV f (bv [] (z≤n {e}) ++bv xs'))) ⟩
    subeq (+ass {e''} {e · e''} {e' · e''})
      (bv [] (z≤n {e''}) ++bv subeq {T = TBV} (dist+ {e} {e'} {e''})
                                    (bindBV f (bv [] (z≤n {e}) ++bv xs')))
  ≡⟨ cong (λ ys → subeq {T = TBV} (+ass {e''} {e · e''} {e' · e''})
                         (bv [] (z≤n {e''}) ++bv ys))
          (lemma-dist (bv [] (z≤n {e})) xs' f) ⟩
    subeq ((+ass {e''} {e · e''} {e' · e''}))
          (bv [] (z≤n {e''}) ++bv (bv [] (z≤n {e · e''}) ++bv bindBV f xs'))
  ≡⟨ lemma-ass++ (bv [] (z≤n {e''})) (bv [] (z≤n {e · e''})) (bindBV f xs') ⟩
    (bv [] (z≤n {e''}) ++bv bv [] (z≤n {e · e''})) ++bv bindBV f xs'
  ≡⟨ cong (λ xs → xs ++bv bindBV f xs') (lemma-[] e'') ⟩
    bv [] (z≤n {suc e · e''}) ++bv bindBV f xs'
  ∎
lemma-dist {suc e} {e'} {e''} (bv (x ∷ xs) (s≤s p)) (bv xs' p') f =
  begin
    subeq {T = TBV} (dist+ {suc e} {e'} {e''})
          (bindBV f (bv (x ∷ xs ++ xs') (mon+ (s≤s p) p')))
  ≡⟨ refl ⟩
    subeq {T = TBV} (dist+ {suc e} {e'} {e''})
          (f x ++bv bindBV f (bv (xs ++ xs') (mon+ p p')))
  ≡⟨ sym (subeq-trans (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                      (+ass {e''} {e · e''} {e' · e''}) _) ⟩
    subeq {T = TBV} (+ass {e''} {e · e''} {e' · e''})
          (subeq {T = TBV} (cong (_+_ e'') (dist+ {e} {e'} {e''}))
                 (f x ++bv bindBV f (bv (xs ++ xs') (mon+ p p'))))
  ≡⟨ cong (subeq {T = TBV} (+ass {e''} {e · e''} {e' · e''}))
          (subeq-lemma (_+_ e'') (_++bv_ (f x)) (dist+ {e} {e'} {e''})
                       (bindBV f (bv (xs ++ xs') (mon+ p p')))) ⟩
    subeq {T = TBV} (+ass {e''} {e · e''} {e' · e''})
          (f x ++bv subeq {T = TBV} (dist+ {e} {e'} {e''})
                          (bindBV f (bv (xs ++ xs') (mon+ p p'))))
  ≡⟨ cong (λ ys → subeq {T = TBV} (+ass {e''} {e · e''} {e' · e''}) (f x ++bv ys))
          (lemma-dist {e} {e'} {e''} (bv xs p) (bv xs' p') f) ⟩
    subeq {T = TBV} (+ass {e''} {e · e''} {e' · e''})
          (f x ++bv (bindBV f (bv xs p) ++bv bindBV f (bv xs' p')))
  ≡⟨ lemma-ass++ (f x) (bindBV f (bv xs p)) (bindBV f (bv xs' p')) ⟩
    (f x ++bv bindBV f (bv xs p)) ++bv bindBV f (bv xs' p')
  ≡⟨ refl ⟩
    bindBV f (bv (x ∷ xs) (s≤s p)) ++bv bindBV f (bv xs' p')
  ∎


mlaw3BV : {e e' e'' : E} {X Y Z : Set} (f : X → TBV e' Y)
        (g : Y → TBV e'' Z) (c : TBV e X) →
        subeq {T = TBV} (ass {e} {e'} {e''}) (bindBV g (bindBV f c)) ≡
        bindBV (λ x → bindBV g (f x)) c
mlaw3BV {e} {e'} {e''} f g (bv [] z≤n) = subeq-air (ass {e} {e'} {e''}) []
mlaw3BV {suc e} {e'} {e''} f g (bv (x ∷ xs) (s≤s p)) = 
  begin
    subeq {T = TBV} (ass {suc e} {e'} {e''}) (bindBV g (bindBV f (bv (x ∷ xs) (s≤s p))))
  ≡⟨ refl ⟩
    subeq {T = TBV} (ass {suc e} {e'} {e''}) (bindBV g (bindBV f (x ∷bv (bv xs p))))
  ≡⟨ refl ⟩
    subeq {T = TBV} (ass {suc e} {e'} {e''}) (bindBV g (f x ++bv bindBV f (bv xs p)))
  ≡⟨ sym (subeq-trans (dist+ {e'} {e · e'} {e''})
                      (cong (_+_ (e' · e'')) (ass {e} {e'} {e''})) _) ⟩
    subeq {T = TBV} (cong (_+_ (e' · e'')) (ass {e} {e'} {e''}))
                    (subeq {T = TBV} (dist+ {e'} {e · e'} {e''})
                           (bindBV g (f x ++bv bindBV f (bv xs p))))
  ≡⟨ cong (subeq {T = TBV} (cong (_+_ (e' · e'')) (ass {e} {e'} {e''})))
                 (lemma-dist (f x) (bindBV f (bv xs p)) g) ⟩
    subeq {T = TBV} (cong (_+_ (e' · e'')) (ass {e} {e'} {e''}))
          (bindBV g (f x) ++bv bindBV g (bindBV f (bv xs p)))
  ≡⟨ subeq-lemma (_+_ (e' · e'')) (_++bv_ (bindBV g (f x))) (ass {e} {e'} {e''}) _ ⟩
    bindBV g (f x) ++bv subeq {T = TBV} (ass {e} {e'} {e''})
                                        (bindBV g (bindBV f (bv xs p)))
  ≡⟨ cong (_++bv_ (bindBV g (f x))) (mlaw3BV f g (bv xs p)) ⟩
    bindBV g (f x) ++bv bindBV (λ x → bindBV g (f x)) (bv xs p)
  ≡⟨ refl ⟩
    bindBV (λ x → bindBV g (f x)) (bv (x ∷ xs) (s≤s p))
  ∎

NDBV : GradedMonad
NDBV = record { OM = ℕ*
              ; T = TBV
              ; η = ηBV
              ; bind = λ {e} {e'} → bindBV {e} {e'}
              ; sub = subBV
              ; sub-mon = subBV-mon
              ; sub-refl = subBV-refl
              ; sub-trans = subBV-trans
              ; mlaw1 = mlaw1BV
              ; mlaw2 = mlaw2BV
              ; mlaw3 = mlaw3BV
              }


-- alias deciders, lub/glb etc.
_≡E?_ = _≟_
_⊑?_ = _≤?_

⊔-sym : (m n : ℕ) → m ⊔ n ≡ n ⊔ m
⊔-sym zero zero = refl
⊔-sym zero (suc n) = refl
⊔-sym (suc m) zero = refl
⊔-sym (suc m) (suc n) = sym (cong suc (⊔-sym n m))

⊓-sym : (m n : ℕ) → m ⊓ n ≡ n ⊓ m
⊓-sym zero zero = refl
⊓-sym zero (suc n) = refl
⊓-sym (suc m) zero = refl
⊓-sym (suc m) (suc n) = sym (cong suc (⊓-sym n m))

_⊹_ = _+_

lub : (m n : ℕ) → m ⊑ (m ⊔ n)
lub zero n = z≤n
lub (suc m) zero = s≤s refl≤
lub (suc m) (suc n) = s≤s (lub m n)

glb : (m n : ℕ) → (m ⊓ n) ⊑ m
glb zero n = z≤n
glb (suc m) zero = z≤n
glb (suc m) (suc n) = s≤s (glb m n)

lub-sym : (m n : ℕ) → m ⊑ (n ⊔ m)
lub-sym m n rewrite ⊔-sym n m = lub m n
