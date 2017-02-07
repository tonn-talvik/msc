module NonDetVec where

open import Function
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


--ru+ : {n : ℕ} → n + 0 ≡ n
--ru+ {zero} = refl
--ru+ {suc n} = cong suc (ru+ {n}) 
ru+ : {n : ℕ} → n ≡ n + 0
ru+ {zero} = refl
ru+ {suc n} = cong suc (ru+ {n}) 

lu* : {n : ℕ} → 1 * n ≡ n
lu* {zero} = refl
lu* {suc n} = cong suc (lu* {n})

ru* : {n : ℕ} → n ≡ n * 1 
ru* {zero} = refl
ru* {suc n} = cong suc (ru* {n})

ass+ : {m n o : ℕ} → (m + n) + o ≡ m + (n + o)
ass+ {zero} = refl
ass+ {suc m} = cong suc (ass+ {m})

+ass : {m n o : ℕ} → m + (n + o) ≡ (m + n) + o
--+ass {m} {n} {o} = sym (ass+ {m} {n} {o})
+ass {zero} = refl
+ass {suc m} = cong suc (+ass {m})

dist+ : {m n o : ℕ} → (m + n) * o ≡ m * o + n * o
dist+ {zero}  {_} {_} = refl
dist+ {suc m} {n} {o} = trans (cong (_+_ o) (dist+ {m} {n} {o})) 
                              (+ass {o} {m * o} {n * o})

ass* : {m n o : ℕ} → (m * n) * o ≡ m * (n * o) -- ⊑
ass* {zero} = refl
ass* {suc m} {n} {o} = trans (dist+ {n} {m * n} {o}) (cong (λ x → n * o + x) (ass* {m} {n} {o}))
{-
                begin
                  (n + m * n) * o
                ≡⟨ dist+ {n} {m * n} {o}  ⟩
                  n * o + (m * n) * o
                ≡⟨ cong (λ x → n * o + x) (ass* {m} {n} {o}) ⟩
                  n * o + m * (n * o)
                ∎
-}

zl* : {m : ℕ} → m * 0 ≡ 0
zl* {zero} = refl
zl* {suc m} = zl* {m}
zr* : {m : ℕ} → 0 ≡ m * 0
zr* {zero} = refl
zr* {suc m} = zr* {m}


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


subV : {n n' : ℕ} {X : Set} → n ⊑ n' → Vec X n → Vec X n'
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


sub-mon : {e e' e'' e''' : M} {X Y : Set} (p : e ⊑ e'') (q : e' ⊑ e''')
      (f : X → Vec Y e') (c : Vec X e) →
      subV (mon p q) (liftV f c) ≡
      liftV ((subV q) ∘ f) (subV p c)
sub-mon refl refl f c = refl 

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

sub-refl : {e : M} {X : Set} (c : Vec X e) → subV reflM c ≡ c
sub-refl _ = refl

sub-trans : {e e' e'' : M} {X : Set} (p : e ⊑ e') (q : e' ⊑ e'')
      (c : Vec X e) →
      subV q (subV p c) ≡ subV (transM p q) c
sub-trans refl refl c = refl
mlaw1V : {n : ℕ} → {X Y : Set} → (f : X → Vec Y n) → (x : X) →
            subV lu (liftV f (ηV x)) ≡ f x
mlaw1V f x = ru++ (f x)


mlaw2V : {n : ℕ} → {X : Set} → (xs : Vec X n) →
            subV ru xs ≡ liftV ηV xs
mlaw2V []       = refl
mlaw2V (x ∷ xs) = subV∷ {x = x} {xs = xs} ru (mlaw2V xs) 

lem1 : {m n : M} → m + suc n ≡ suc m + n
lem1 {zero} = refl
lem1 {suc m} {n} = cong suc (lem1 {m})

comm+ : {m n : M} → m + n ≡ n + m
comm+ {zero} = ru+
comm+ {suc m} {zero} = cong suc (comm+ {m})
comm+ {suc m} {suc n} = cong suc (
  begin
    m + suc n
  ≡⟨ lem1 {m} {n} ⟩
    suc m + n
  ≡⟨ comm+ {suc m} ⟩
    n + suc m 
  ∎)

-- FIXME :-)
comm* : {m n : M} → m * n ≡ n * m
comm* {zero} {n} = zr* {n}
comm* {suc m} {zero} = comm* {m}
comm* {suc m} {suc n} = cong suc (
  begin
    n + m * suc n
  ≡⟨ cong (_+_ n) (comm* {m}) ⟩
    n + suc n * m
  ≡⟨ cong (_+_ n) (comm+ {m}) ⟩
    n + (n * m + m)
  ≡⟨ cong (_+_ n) (cong (λ x → x + m) (comm* {n})) ⟩
    n + (m * n + m)
  ≡⟨ sym (ass+ {n}) ⟩
    (n + m * n) + m
  ≡⟨ comm+ {n + m * n} ⟩
    m + suc m * n
  ≡⟨ cong (_+_ m) (comm* {suc m} {n}) ⟩
    m + n * suc m
  ∎)


lemma-sub++ : {e e' E E' : M} 
             {p : e ⊑ E} {q : e' ⊑ E'} {r : (e + e') ⊑ (E + E')}
             {X : Set}
             (xs : Vec X e) (xs' : Vec X e') →
             subV p xs ++ subV q xs' ≡ subV r (xs ++ xs')
lemma-sub++ {p = refl} {q = refl} {r = refl} [] xs' = refl
lemma-sub++ {suc e} {e'} {E = suc .e} {E' = .e'} {p = refl} {q = refl} {r = refl} (x ∷ xs) xs' = 
  begin
    subV refl (x ∷ xs) ++ subV refl xs'
  ≡⟨ refl ⟩
    x ∷ (subV refl xs) ++ subV refl xs'
  ≡⟨ cong (_∷_ x) (lemma-sub++ {p = refl} {q = refl} {r = cong (_+_ e) refl} xs xs') ⟩
    x ∷ (subV (cong (_+_ e) refl) (xs ++ xs'))
  ≡⟨ sym (subV∷ (cong (_+_ e) refl) refl) ⟩
    subV (cong suc (cong (_+_ e) refl)) (x ∷ xs ++ xs')
  ≡⟨ refl ⟩
    subV refl (x ∷ xs ++ xs')
  ∎

ass+* : {m n o : ℕ} → n * o + m * n * o ≡ n * o + m * (n * o) --suc m * (n * o)
ass+* {m} {n} {o} = cong (_+_ (n * o)) (ass* {m} {n} {o})

lemma++ : {e e' e'' : M} {X : Set}
          (xs : Vec X e) (xs' : Vec X e') (xs'' : Vec X e'') →
          subV (+ass {e} {e'} {e''}) (xs ++ (xs' ++ xs''))
          ≡ (xs ++ xs') ++ xs''
lemma++ [] xs' xs'' = refl
lemma++ {suc e} {e'} {e''} (x ∷ xs) xs' xs'' = subV∷ (+ass {e} {e'} {e''}) (lemma++ xs xs' xs'')

lemma-11 : {e e' e'' : M} →
           (e'' + (e' * e'' + e * suc e' * e'')) ⊑
           (e'' + e' * e'' + e * (e'' + e' * e''))
lemma-11 {e} {e'} {e''} = 
  begin
    e'' + (e' * e'' + e * suc e' * e'')
  ≡⟨ +ass {e''} {e' * e''} {e * suc e' * e''} ⟩
    (e'' + e' * e'') + e * suc e' * e''
  ≡⟨ cong (_+_ (e'' + e' * e'')) (
          begin
            e * suc e' * e''
          ≡⟨ ass* {e} {suc e'} {e''} ⟩
            e * (suc e' * e'')
          ≡⟨ refl ⟩
            e * (e'' + e' * e'')
          ∎) ⟩
    e'' + e' * e'' + e * (e'' + e' * e'')
  ∎


lemma-cong0+ : {e e' : M} {p : e ≡ e'} → 
               cong (_+_ 0) p ≡ p
lemma-cong0+ {p = refl} = refl

lemma-trans : {e e' : M} {p : e ≡ e'} →
              trans p refl ≡ p
lemma-trans {p = refl} = refl

lemma-ass* : {e e'' : M} →
            ass* {suc e} {zero} {e''}
            ≡ ass* {e} {zero} {e''}
lemma-ass* {zero} = refl
lemma-ass* {suc e} {e''} rewrite lemma-ass* {e} {e''}
    with lemma-cong0+ {p = ass* {e} {zero} {e''}}
... | p rewrite p = refl -- lemma-trans

lemma-other : {e e' : M} →
              trans (cong (_+_ zero) (dist+ {e} {e'} {zero})) refl
              ≡ dist+ {e} {e'} {zero}
lemma-other = trans lemma-trans lemma-cong0+

lemma-sym-cong : {X : Set} {x x' : X} {f : X → X} {p : x ≡ x'} →
                 sym (cong f p) ≡ cong f (sym p)
lemma-sym-cong {p = refl} = refl

lemma-trans-cong : {X : Set} {x x' x'' : X}
                   {f : X → X} {p : x ≡ x'} {q : x' ≡ x''} →
                   trans (cong f p) (cong f q) ≡ cong f (trans p q)
lemma-trans-cong {p = refl} = refl

lemma-suc : {m n n' : M} {p : n ≡ n'} →
            cong (_+_ (suc m)) p ≡ cong suc (cong (_+_ m) p)
lemma-suc {p = refl} = refl

lemma-some  : {e e' e'' : M} →
              trans (cong (_+_ (suc e''))
                          (dist+ {e} {e'} {suc e''}))
                    (sym (cong suc (ass+ {e''} {e * suc e''} {e' * suc e''})))
              ≡
              cong suc (trans (cong (_+_ e'')
                                    (dist+ {e} {e'} {suc e''}))
                          (sym (ass+ {e''} {e * suc e''} {e' * suc e''})))
lemma-some {e} {e'} {e''} = 
  begin
    trans (cong (_+_ (suc e''))
                (dist+ {e} {e'} {suc e''}))
          (sym (cong suc (ass+ {e''} {e * suc e''} {e' * suc e''})))
  ≡⟨ cong (trans (cong (_+_ (suc e'')) (dist+ {e} {e'} {suc e''})))
          lemma-sym-cong ⟩
    trans (cong (_+_ (suc e''))
                (dist+ {e} {e'} {suc e''}))
          (cong suc (sym (ass+ {e''} {e * suc e''} {e' * suc e''})))
  ≡⟨ cong (λ p → trans p (cong suc (sym (ass+ {e''} {e * suc e''} {e' * suc e''}))))
          (lemma-suc {m = e''} {p = dist+ {e} {e'} {suc e''}}) ⟩
    trans (cong suc (cong (_+_ e'')
                          (dist+ {e} {e'} {suc e''})))
          (cong suc (sym (ass+ {e''} {e * suc e''} {e' * suc e''})))
  ≡⟨ lemma-trans-cong {p = cong (_+_ e'') (dist+ {e} {e'} {suc e''})} ⟩
    cong suc (trans (cong (_+_ e'')
                          (dist+ {e} {e'} {suc e''}))
                    (sym (ass+ {e''} {e * suc e''} {e' * suc e''})))
  ∎
            
lemma-head : {X : Set} {x : X} {e e' e'' : M}
             {xs : Vec X e} {xs' : Vec X e'}
             {p : e ≡ e''} {q : e' ≡ e''}
             {tail : subV p xs ≡ subV q xs'} →
             subV (cong suc p) (x ∷ xs)
             ≡ subV (cong suc q) (x ∷ xs')
lemma-head {p = refl} {q = refl} {tail = refl} = refl
  
{-                          
lemma-that : {e e' e'' : M} {X Y : Set}
             (ys : Vec Y e'')
             (xs : Vec X e)
             (xs' : Vec X e')
             (f : X → Vec Y e'') →
             subV (dist+ {suc e} {e'} {e''})
                  (ys ++ liftV f (xs ++ xs'))
             ≡ subV (+ass {e''} {e * e''} {e' * e''})
                    (ys ++ subV (dist+ {e} {e'} {e''}) (liftV f (xs ++ xs')))
lemma-that {e} {e'} {zero} [] xs xs' f =
               cong (λ p → subV p (liftV f (xs ++ xs')))
                    (lemma-other {e} {e'}) 
lemma-that {e} {e'} {suc e''} (y ∷ ys) xs xs' f =
  begin
    subV (dist+ {suc e} {e'} {suc e''})
         (y ∷ ys ++ liftV f (xs ++ xs'))
  ≡⟨ refl ⟩ 
    subV (trans (cong (_+_ (suc e'')) (dist+ {e} {e'} {suc e''}))
                (sym (cong suc (ass+ {e''} {e * suc e''} {e' * suc e''}))))
         (y ∷ ys ++ liftV f (xs ++ xs'))
  ≡⟨ cong (λ p → subV p (y ∷ ys ++ liftV f (xs ++ xs'))) (lemma-some {e}) ⟩
    subV (cong suc (trans (cong (_+_ e'')
                                (dist+ {e} {e'} {suc e''}))
                          (sym (ass+ {e''} {e * suc e''} {e' * suc e''}))))
         (y ∷ ys ++ liftV f (xs ++ xs'))
  ≡⟨ lemma-head {tail = lemma-that ys {!!} {!!} {!!}}  ⟩ -- sigh
    subV (cong suc (+ass {e''} {e * suc e''} {e' * suc e''}))
         (y ∷ ys ++ subV (dist+ {e} {e'} {suc e''}) (liftV f (xs ++ xs')))
  ≡⟨ refl ⟩
    subV (+ass {suc e''} {e * suc e''} {e' * suc e''})
         (y ∷ ys ++ subV (dist+ {e} {e'} {suc e''}) (liftV f (xs ++ xs')))
  ∎
-}
{- long version of base case
lemma-that {e} {e'} {zero} [] xs xs' f =
  begin
    subV (dist+ {suc e} {e'} {zero})
         ([] ++ liftV f (xs ++ xs'))
  ≡⟨ cong (λ p → subV p (liftV f (xs ++ xs'))) (lemma-other {e} {e'}) ⟩
    subV refl
         (subV (dist+ {e} {e'} {zero}) (liftV f (xs ++ xs')))
  ≡⟨ refl ⟩
    subV (+ass {zero} {e * zero} {e' * zero})
         (subV (dist+ {e} {e'} {zero}) (liftV f (xs ++ xs')))
  ≡⟨ refl ⟩
    subV (+ass {zero} {e * zero} {e' * zero})
         ([] ++ subV (dist+ {e} {e'} {zero}) (liftV f (xs ++ xs')))
  ∎-}

{-

lemma-ass : {m n o : M} →
            sym (ass+ {m} {n} {o}) ≡ +ass {m} {n} {o}
lemma-ass {zero} = refl
lemma-ass {suc m} = 
  begin
    sym (cong suc (ass+ {m}))
  ≡⟨ {!!} ⟩
    cong suc (+ass {m})
  ∎

lemma-that2 : {e e' e'' : M} {X Y : Set}
             (xs : Vec X e)
             (xs' : Vec X e')
             (ys : Vec Y e'')
             (f : X → Vec Y e'') →
             subV (dist+ {suc e} {e'} {e''})
                  (ys ++ liftV f (xs ++ xs'))
             ≡ subV (sym (ass+ {e''} {e * e''} {e' * e''}))
                    (ys ++ subV (dist+ {e} {e'} {e''}) (liftV f (xs ++ xs')))
lemma-that2 {zero} {e'} {e''} [] xs' ys f = refl
lemma-that2 {suc e} {e'} {e''} (x ∷ xs) xs' ys f = 
  begin
    subV (dist+ {suc (suc e)} {e'} {e''})
         (ys ++ liftV f (x ∷ xs ++ xs'))
  ≡⟨ refl ⟩
    subV (dist+ {suc (suc e)} {e'} {e''})
         (ys ++ f x ++ liftV f (xs ++ xs'))
  ≡⟨ {!!} ⟩
    subV {!!}
         (ys ++ f x ++ subV (dist+ {e} {e'} {e''}) (liftV f (xs ++ xs')))
  ≡⟨ {!!} ⟩
    subV (sym (ass+ {e''} {suc e * e''} {e' * e''}))
         (ys ++ subV (dist+ {suc e} {e'} {e''}) (f x ++ liftV f (xs ++ xs')))
  ≡⟨ refl ⟩
    subV (sym (ass+ {e''} {suc e * e''} {e' * e''}))
         (ys ++ subV (dist+ {suc e} {e'} {e''}) (liftV f (x ∷ xs ++ xs')))
  ∎
-}

lemma-dist : {e e' e'' : M} {X Y : Set}
             (xs : Vec X e)
             (xs' : Vec X e')
             (f : X → Vec Y e'') →
             subV (dist+ {e} {e'} {e''}) (liftV f (xs ++ xs'))
             ≡ liftV f xs ++ liftV f xs'
lemma-dist [] xs' f = refl
lemma-dist {suc e} {e'} {e''} (x ∷ xs) xs' f =
  begin
    subV (dist+ {suc e} {e'} {e''}) (liftV f (x ∷ xs ++ xs'))
  ≡⟨ refl ⟩
    subV (dist+ {suc e} {e'} {e''}) (f x ++ (liftV f (xs ++ xs')))
  ≡⟨ {!!} ⟩
    subV (+ass {e''} {e * e''} {e' * e''})
         (f x ++ subV (dist+ {e} {e'} {e''}) (liftV f (xs ++ xs')))
  ≡⟨ cong (λ ys → subV (+ass {e''} {e * e''} {e' * e''}) (f x ++ ys))
          (lemma-dist {e} {e'} {e''} xs xs' f) ⟩ 
    subV (+ass {e''} {e * e''} {e' * e''}) (f x ++ (liftV f xs ++ liftV f xs'))
  ≡⟨ lemma++ (f x) (liftV f xs) (liftV f xs') ⟩
    (f x ++ liftV f xs) ++ liftV f xs'
  ≡⟨ refl ⟩
    liftV f (x ∷ xs) ++ liftV f xs'
  ∎

lemma : {e e' e'' : M} {Y Z : Set}
        (g : Y → Vec Z e'')
        (ys : Vec Y e')
        (ys' : Vec Y (e * e')) →
        subV (ass* {suc e} {e'} {e''}) (liftV g (ys ++ ys'))
        ≡ liftV g ys ++ subV (ass* {e} {e'} {e''}) (liftV g ys')
lemma {e} {zero} {e''} g [] ys' = cong (λ p → subV p (liftV g ys'))
                                           (lemma-ass* {e} {e''})
lemma {e} {suc e'} {e''} g (y ∷ ys) ys' = 
  begin
    subV (ass* {suc e} {suc e'} {e''}) (liftV g ((y ∷ ys) ++ ys'))
  ≡⟨ refl ⟩
    subV (ass* {suc e} {suc e'} {e''}) (g y ++ (liftV g (ys ++ ys')))
  ≡⟨ {!!} ⟩
  -- congruent with lemma on recursively smaller ys
  -- pitfall: ys' did not shrink, but it is tied to the ys by e'
  
    subV (+ass {e''} {e' * e''} {e * (suc e' * e'')})
         (g y ++ (liftV g ys ++ subV (ass* {e} {suc e'} {e''}) (liftV g ys')))
  ≡⟨ lemma++ (g y) (liftV g ys) (subV (ass* {e} {suc e'} {e''}) (liftV g ys')) ⟩
    (g y ++ liftV g ys) ++ subV (ass* {e} {suc e'} {e''}) (liftV g ys')
  ≡⟨ refl ⟩
    liftV g (y ∷ ys) ++ subV (ass* {e} {suc e'} {e''}) (liftV g ys')
  ∎


subV-lemma : {e e' : M} {X Y : Set} → (g : M → M) → (f : {e : M} → Vec X e → Vec Y (g e))
      → (p : e ≡ e') → (xs : Vec X e) → subV (cong g p) (f xs) ≡ f (subV p xs)
subV-lemma g f refl xs =  refl


mlaw3V : {e e' e'' : M} {X Y Z : Set} (f : X → Vec Y e')
      (g : Y → Vec Z e'') (c : Vec X e) →
      subV (ass* {e} {e'} {e''}) (liftV g (liftV f c))
      ≡ liftV (λ x → liftV g (f x)) c
mlaw3V f g [] = refl
mlaw3V {suc e} {e'} {e''} f g (x ∷ xs) =
  begin
    subV (ass* {suc e} {e'} {e''}) (liftV g (liftV f (x ∷ xs)))
  ≡⟨ refl ⟩
    subV (ass* {suc e} {e'} {e''}) (liftV g (f x ++ liftV f xs))
  ≡⟨ sym (sub-trans (dist+ {e'} {e * e'} {e''}) (cong (_+_ (e' * e'')) (ass* {e} {e'} {e''})) _)  ⟩
    subV (cong (_+_ (e' * e'')) (ass* {e} {e'} {e''}))
       (subV (dist+ {e'} {e * e'} {e''}) (liftV g (f x ++ liftV f xs)))
  ≡⟨  cong (subV (cong (_+_ (e' * e'')) (ass* {e} {e'} {e''}))) (lemma-dist (f x) (liftV f xs) g) ⟩ 
    subV (cong (_+_ (e' * e'')) (ass* {e} {e'} {e''}))
        (liftV g (f x) ++ liftV g (liftV f xs))
  ≡⟨ subV-lemma (_+_ (e' * e'')) (_++_ (liftV g (f x))) (ass* {e} {e'} {e''}) _  ⟩ 
     (liftV g (f x) ++ subV (ass* {e} {e'} {e''}) (liftV g (liftV f xs)))
  ≡⟨ cong (_++_ (liftV g (f x))) (mlaw3V f g xs) ⟩
    liftV g (f x) ++ liftV (λ x → liftV g (f x)) xs
  ≡⟨ refl ⟩
    liftV (λ x → liftV g (f x)) (x ∷ xs)
  ∎

NDV : GradedMonad
NDV = record { OM = ℕ*
                 ; T = λ e X → Vec X e
                 ; η = ηV
                 ; lift = liftV 
                 ; sub = subV 
                 ; sub-mon = sub-mon
                 ; sub-refl = sub-refl
                 ; sub-trans = sub-trans
                 ; mlaw1 = mlaw1V
                 ; mlaw2 = mlaw2V
                 ; mlaw3 = mlaw3V
                 }
