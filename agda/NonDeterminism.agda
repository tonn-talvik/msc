module NonDeterminism where

open import Function
open import Data.List
open import Relation.Nullary


open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality hiding ([_]; inspect)

open import Finiteness
open import OrderedMonoid
open import GradedMonad


data ND : Set where
  nd0  : ND
  nd01 : ND
  nd1  : ND
  nd1+ : ND
  ndN  : ND

data _⊑ND_ : ND → ND → Set where
  reflND : {m : ND} → m ⊑ND m
  topND : {m : ND} → m ⊑ND ndN
  0⊑01 : nd0 ⊑ND nd01
  1⊑01 : nd1 ⊑ND nd01
  1⊑1+ : nd1 ⊑ND nd1+

_⊙_ : ND → ND → ND
nd0 ⊙ n = nd0
nd01 ⊙ nd0 = nd0
nd01 ⊙ nd01 = nd01
nd01 ⊙ nd1 = nd01
nd01 ⊙ nd1+ = ndN
nd01 ⊙ ndN = ndN
nd1 ⊙ n = n
nd1+ ⊙ nd0 = nd0
nd1+ ⊙ nd01 = ndN
nd1+ ⊙ nd1 = nd1+
nd1+ ⊙ nd1+ = nd1+
nd1+ ⊙ ndN = ndN
ndN ⊙ nd0 = nd0
ndN ⊙ _ = ndN

-------------------------------------------------------

_?⊑ND_ : (m : ND) → (n : ND) → Dec (m ⊑ND n)
nd0 ?⊑ND nd0 = yes reflND
nd0 ?⊑ND nd01 = yes 0⊑01
nd0 ?⊑ND nd1 = no (λ ())
nd0 ?⊑ND nd1+ = no (λ ())
nd0 ?⊑ND ndN = yes topND
nd01 ?⊑ND nd0 = no (λ ())
nd01 ?⊑ND nd01 = yes reflND
nd01 ?⊑ND nd1 = no (λ ())
nd01 ?⊑ND nd1+ = no (λ ())
nd01 ?⊑ND ndN = yes topND
nd1 ?⊑ND nd0 = no (λ ())
nd1 ?⊑ND nd01 = yes 1⊑01
nd1 ?⊑ND nd1 = yes reflND
nd1 ?⊑ND nd1+ = yes 1⊑1+
nd1 ?⊑ND ndN = yes topND
nd1+ ?⊑ND nd0 = no (λ ())
nd1+ ?⊑ND nd01 = no (λ ())
nd1+ ?⊑ND nd1 = no (λ ())
nd1+ ?⊑ND nd1+ = yes reflND
nd1+ ?⊑ND ndN = yes topND
ndN ?⊑ND nd0 = no (λ ())
ndN ?⊑ND nd01 = no (λ ())
ndN ?⊑ND nd1 = no (λ ())
ndN ?⊑ND nd1+ = no (λ ())
ndN ?⊑ND ndN = yes reflND 

private 

  listND : List ND
  listND = nd0 ∷ nd01 ∷ nd1 ∷ nd1+ ∷ ndN ∷ [] 

  cmpltND : (x : ND) → x ∈ listND
  cmpltND nd0  = here
  cmpltND nd01 = there here
  cmpltND nd1  = there (there here)
  cmpltND nd1+ = there (there (there here))
  cmpltND ndN  = there (there (there (there here)))


lstblND : Listable ND 
lstblND = record { list = listND
                 ; complete = cmpltND
                 }

infix 10 _?≡ND_ 

_?≡ND_ : (m : ND) → (n : ND) → Dec (m ≡ n)
_?≡ND_ = ?≡L lstblND

?∀ND : {P : ND → Set} → ((m : ND) → Dec (P m)) → Dec ((m : ND) → P m)
?∀ND = ?∀ lstblND

-------------------------------------------------------

private 
  refl-⊑ND : (m : ND) → m ⊑ND m
  refl-⊑ND = extract (?∀ND (λ m → m ?⊑ND m))

  trans-⊑ND : (m n o : ND) → m ⊑ND n → n ⊑ND o → m ⊑ND o
  trans-⊑ND = extract (?∀ND (λ m → 
                         ?∀ND (λ n → 
                           ?∀ND (λ o →   
                                  (m ?⊑ND n) ?→ ((n ?⊑ND o) ?→ (m ?⊑ND o))))))

  ru-⊙ : (m : ND) → m ≡ m ⊙ nd1
  ru-⊙ = extract (?∀ND (λ m → m ?≡ND m  ⊙ nd1))


  mon-⊙ : (m n m' n' : ND) →  m ⊑ND m' → n ⊑ND n' → (m ⊙ n) ⊑ND (m' ⊙ n')
  mon-⊙ = extract (?∀ND (λ m → 
                     ?∀ND (λ n → 
                       ?∀ND (λ m' → 
                         ?∀ND (λ n' →
                                (m ?⊑ND m') ?→ ((n ?⊑ND n') ?→ ((m ⊙ n) ?⊑ND (m' ⊙ n'))) )))))
                                  
  ass-⊙ : (m n o : ND) → (m ⊙ n) ⊙ o ≡ m ⊙ (n ⊙ o)
  ass-⊙ = extract (?∀ND (λ m → 
                     ?∀ND (λ n → 
                       ?∀ND (λ o →
                              ((m ⊙ n) ⊙ o) ?≡ND (m ⊙ (n ⊙ o)) ))))


NDEffOM : OrderedMonoid
NDEffOM = record { M = ND
                 ; _⊑_ = _⊑ND_
                 ; reflM = λ {m} → refl-⊑ND m
                 ; transM = λ {m} {n} {o} → trans-⊑ND m n o
                 ; i = nd1
                 ; _·_ = _⊙_ -- \odot ⊙
                 ; mon = λ {m} {n} {m'} {n'} → mon-⊙ m n m' n'
                 ; lu = refl
                 ; ru = λ {m} → ru-⊙ m
                 ; ass = λ {m} {n} {o} → ass-⊙ m n o
                 }
                 
-------------------------------------------------------


open import Data.List

private 
  TND : ND → Set → Set
  TND nd X = List X  -- powerset?

  ηND : {X : Set} → X → TND (nd1) X
  ηND x = [ x ]

  liftND :  (e e' : ND) {X Y : Set} →
        (X → TND e' Y) → TND e X → TND (e ⊙ e') Y
  liftND _ _ f [] = []
  liftND e e' f (x ∷ xs) = (f x) ++ (liftND e e' f xs)

  -- Is this correct? Isn't TND too broad?
  subND : {e e' : ND} {X : Set} → e ⊑ND e' → TND e X → TND e' X
  subND p x = x

  subND-refl : {e : ND} {X : Set} → (c : TND e X) → subND {e} reflND c ≡ c
  subND-refl _ = refl

  subND-mon : {e e' e'' e''' : ND} {X Y : Set} →
              (p : e ⊑ND e'') → (q : e' ⊑ND e''') →
              (f : X → TND e' Y) → (c : TND e X) → 
              subND (mon-⊙ e e' e'' e''' p q) (liftND e e' f c) ≡ liftND e'' e''' (subND q ∘ f) (subND p c)
  subND-mon p q f c = refl



  subND-trans : {e e' e'' : ND} {X : Set} →
                (p : e ⊑ND e') → (q : e' ⊑ND e'') → (c : TND e X) → 
                subND q (subND p c) ≡ subND (trans-⊑ND e e' e'' p q) c
  subND-trans r q c = refl


  ++-right-identity : {X : Set} (xs : List X) → xs ++ [] ≡ xs
  ++-right-identity [] = refl
  ++-right-identity (x ∷ xs) = cong (_∷_ x) (++-right-identity xs)

  mlaw1ND : {e : ND} → {X Y : Set} → (f : X → TND e Y) → (x : X) →
            liftND nd1 e f (ηND x) ≡ f x
  mlaw1ND f x = ++-right-identity (f x)



  subND-eq : {e e' : ND} {X : Set} → e ≡ e' → TND e X → TND e' X
  subND-eq = subeq {ND} {TND}


  η-lift-identity : {e e' : ND} {X : Set} (xs : List X) → xs ≡ liftND e e' ηND xs
  η-lift-identity [] = refl
  η-lift-identity {e} {e'} (x ∷ xs) = cong (_∷_ x) (η-lift-identity {e} {e'} xs)

  mlaw2ND :  {e : ND} → {X : Set} → (c : TND e X) →
             subND-eq {e} (ru-⊙ e) c ≡ liftND e nd1 ηND c
  mlaw2ND {nd0} [] = refl
  mlaw2ND {nd01} [] = refl
  mlaw2ND {nd1} [] = refl
  mlaw2ND {nd1+} [] = refl
  mlaw2ND {ndN} [] = refl
  mlaw2ND {nd0} (x ∷ xs) = cong (_∷_ x) (η-lift-identity xs)
  mlaw2ND {nd01} (x ∷ xs) = cong (_∷_ x) (η-lift-identity xs)
  mlaw2ND {nd1} (x ∷ xs) = cong (_∷_ x) (η-lift-identity xs)
  mlaw2ND {nd1+} (x ∷ xs) = cong (_∷_ x) (η-lift-identity xs)
  mlaw2ND {ndN} (x ∷ xs) = cong (_∷_ x) (η-lift-identity xs)


lemma++ : {X : Set} (xs xs' xs'' : List X) →
          xs ++ (xs' ++ xs'') ≡ (xs ++ xs') ++ xs''
lemma++ [] xs' xs'' = refl
lemma++ (x ∷ xs) xs' xs'' rewrite lemma++ xs xs' xs'' = refl

lemma-liftND : {e e' : ND} {X Y : Set} → (f : X → TND e' Y) → (xs xs' : TND e X) → 
    liftND e e' f (xs ++ xs') ≡ liftND e e' f xs ++ liftND e e' f xs'
lemma-liftND f [] xs' = refl
lemma-liftND {e} {e'} f (x ∷ xs) xs' rewrite lemma-liftND {e} {e'} f xs xs' = lemma++ (f x) (liftND e e' f xs) (liftND e e' f xs')

mlaw3ND' : (e e' e'' : ND) → {X Y Z : Set} →
          (f : X → TND e' Y) → (g : Y → TND e'' Z) → (c : TND e X) → 
          (liftND (e ⊙ e') e'' g (liftND e e' f c))
          ≡ liftND e (e' ⊙ e'') (λ x → liftND e' e'' g (f x)) c
mlaw3ND' e e' e'' f g [] = refl
mlaw3ND' e e' e'' f g (c ∷ cs) = trans (lemma-liftND {e ⊙ e'} {e''} g (f c) (liftND e e' f cs)) (cong (_++_ (liftND e' e'' g (f c))) (mlaw3ND' e e' e'' f g cs))

--subND-eq : {e e' : ND} {X : Set} → e ≡ e' → TND e X → TND e' X
--subND-eq refl p = p

lemma-s : {e e' : ND} {X : Set} → (p : e ≡ e') →
          (c : TND e X) → (d : TND e' X) → subND-eq p c ≡ d
lemma-s refl c d = {!!}

lemma : (e e' e'' : ND) → {X Y Z : Set} →
        (f : X → TND e' Y) → (g : Y → TND e'' Z) → (xs : TND e X) → 
        subND-eq (ass-⊙ e e' e'')
                 (liftND (e ⊙ e') e'' g (liftND e e' f xs))
        ≡ liftND (e ⊙ e') e'' g (liftND e e' f xs)
-- note to self: should look for a job in agriculture
{-
lemma nd0 nd0 nd0 f g [] = refl
lemma nd0 nd0 nd01 f g [] = refl
lemma nd0 nd0 nd1 f g [] = refl
lemma nd0 nd0 nd1+ f g [] = refl
lemma nd0 nd0 ndN f g [] = refl
lemma nd0 nd01 nd0 f g [] = refl
lemma nd0 nd01 nd01 f g [] = refl
lemma nd0 nd01 nd1 f g [] = refl
lemma nd0 nd01 nd1+ f g [] = refl
lemma nd0 nd01 ndN f g [] = refl
lemma nd0 nd1 nd0 f g [] = refl
lemma nd0 nd1 nd01 f g [] = refl
lemma nd0 nd1 nd1 f g [] = refl
lemma nd0 nd1 nd1+ f g [] = refl
lemma nd0 nd1 ndN f g [] = refl
lemma nd0 nd1+ nd0 f g [] = refl
lemma nd0 nd1+ nd01 f g [] = refl
lemma nd0 nd1+ nd1 f g [] = refl
lemma nd0 nd1+ nd1+ f g [] = refl
lemma nd0 nd1+ ndN f g [] = refl
lemma nd0 ndN nd0 f g [] = refl
lemma nd0 ndN nd01 f g [] = refl
lemma nd0 ndN nd1 f g [] = refl
lemma nd0 ndN nd1+ f g [] = refl
lemma nd0 ndN ndN f g [] = refl
lemma nd01 nd0 nd0 f g [] = refl
lemma nd01 nd0 nd01 f g [] = refl
lemma nd01 nd0 nd1 f g [] = refl
lemma nd01 nd0 nd1+ f g [] = refl
lemma nd01 nd0 ndN f g [] = refl
lemma nd01 nd01 nd0 f g [] = refl
lemma nd01 nd01 nd01 f g [] = refl
lemma nd01 nd01 nd1 f g [] = refl
lemma nd01 nd01 nd1+ f g [] = refl
lemma nd01 nd01 ndN f g [] = refl
lemma nd01 nd1 nd0 f g [] = refl
lemma nd01 nd1 nd01 f g [] = refl
lemma nd01 nd1 nd1 f g [] = refl
lemma nd01 nd1 nd1+ f g [] = refl
lemma nd01 nd1 ndN f g [] = refl
lemma nd01 nd1+ nd0 f g [] = refl
lemma nd01 nd1+ nd01 f g [] = refl
lemma nd01 nd1+ nd1 f g [] = refl
lemma nd01 nd1+ nd1+ f g [] = refl
lemma nd01 nd1+ ndN f g [] = refl
lemma nd01 ndN nd0 f g [] = refl
lemma nd01 ndN nd01 f g [] = refl
lemma nd01 ndN nd1 f g [] = refl
lemma nd01 ndN nd1+ f g [] = refl
lemma nd01 ndN ndN f g [] = refl
lemma nd1 nd0 nd0 f g [] = refl
lemma nd1 nd0 nd01 f g [] = refl
lemma nd1 nd0 nd1 f g [] = refl
lemma nd1 nd0 nd1+ f g [] = refl
lemma nd1 nd0 ndN f g [] = refl
lemma nd1 nd01 nd0 f g [] = refl
lemma nd1 nd01 nd01 f g [] = refl
lemma nd1 nd01 nd1 f g [] = refl
lemma nd1 nd01 nd1+ f g [] = refl
lemma nd1 nd01 ndN f g [] = refl
lemma nd1 nd1 nd0 f g [] = refl
lemma nd1 nd1 nd01 f g [] = refl
lemma nd1 nd1 nd1 f g [] = refl
lemma nd1 nd1 nd1+ f g [] = refl
lemma nd1 nd1 ndN f g [] = refl
lemma nd1 nd1+ nd0 f g [] = refl
lemma nd1 nd1+ nd01 f g [] = refl
lemma nd1 nd1+ nd1 f g [] = refl
lemma nd1 nd1+ nd1+ f g [] = refl
lemma nd1 nd1+ ndN f g [] = refl
lemma nd1 ndN nd0 f g [] = refl
lemma nd1 ndN nd01 f g [] = refl
lemma nd1 ndN nd1 f g [] = refl
lemma nd1 ndN nd1+ f g [] = refl
lemma nd1 ndN ndN f g [] = refl
lemma nd1+ nd0 nd0 f g [] = refl
lemma nd1+ nd0 nd01 f g [] = refl
lemma nd1+ nd0 nd1 f g [] = refl
lemma nd1+ nd0 nd1+ f g [] = refl
lemma nd1+ nd0 ndN f g [] = refl
lemma nd1+ nd01 nd0 f g [] = refl
lemma nd1+ nd01 nd01 f g [] = refl
lemma nd1+ nd01 nd1 f g [] = refl
lemma nd1+ nd01 nd1+ f g [] = refl
lemma nd1+ nd01 ndN f g [] = refl
lemma nd1+ nd1 nd0 f g [] = refl
lemma nd1+ nd1 nd01 f g [] = refl
lemma nd1+ nd1 nd1 f g [] = refl
lemma nd1+ nd1 nd1+ f g [] = refl
lemma nd1+ nd1 ndN f g [] = refl
lemma nd1+ nd1+ nd0 f g [] = refl
lemma nd1+ nd1+ nd01 f g [] = refl
lemma nd1+ nd1+ nd1 f g [] = refl
lemma nd1+ nd1+ nd1+ f g [] = refl
lemma nd1+ nd1+ ndN f g [] = refl
lemma nd1+ ndN nd0 f g [] = refl
lemma nd1+ ndN nd01 f g [] = refl
lemma nd1+ ndN nd1 f g [] = refl
lemma nd1+ ndN nd1+ f g [] = refl
lemma nd1+ ndN ndN f g [] = refl
lemma ndN nd0 nd0 f g [] = refl
lemma ndN nd0 nd01 f g [] = refl
lemma ndN nd0 nd1 f g [] = refl
lemma ndN nd0 nd1+ f g [] = refl
lemma ndN nd0 ndN f g [] = refl
lemma ndN nd01 nd0 f g [] = refl
lemma ndN nd01 nd01 f g [] = refl
lemma ndN nd01 nd1 f g [] = refl
lemma ndN nd01 nd1+ f g [] = refl
lemma ndN nd01 ndN f g [] = refl
lemma ndN nd1 nd0 f g [] = refl
lemma ndN nd1 nd01 f g [] = refl
lemma ndN nd1 nd1 f g [] = refl
lemma ndN nd1 nd1+ f g [] = refl
lemma ndN nd1 ndN f g [] = refl
lemma ndN nd1+ nd0 f g [] = refl
lemma ndN nd1+ nd01 f g [] = refl
lemma ndN nd1+ nd1 f g [] = refl
lemma ndN nd1+ nd1+ f g [] = refl
lemma ndN nd1+ ndN f g [] = refl
lemma ndN ndN nd0 f g [] = refl
lemma ndN ndN nd01 f g [] = refl
lemma ndN ndN nd1 f g [] = refl
lemma ndN ndN nd1+ f g [] = refl
lemma ndN ndN ndN f g [] = refl
-}
lemma e e' e'' f g [] = {!!}
lemma e e' e'' f g (x ∷ xs) with f x
lemma e e' e'' f g (x ∷ xs) | [] = {!!}
lemma e e' e'' f g (x ∷ xs) | x₁ ∷ c = {!!}


mlaw3ND : (e e' e'' : ND) → {X Y Z : Set} →
          (f : X → TND e' Y) → (g : Y → TND e'' Z) → (c : TND e X) → 
          subND-eq {(e ⊙ e') ⊙ e''} {e ⊙ (e' ⊙ e'')}
                   (ass-⊙ e e' e'')
                   (liftND (e ⊙ e') e'' g (liftND e e' f c))
          ≡ liftND e (e' ⊙ e'') (λ x → liftND e' e'' g (f x)) c
mlaw3ND e e' e'' f g c = trans (lemma e e' e'' f g c) (mlaw3ND' e e' e'' f g c)


NDEffGM : GradedMonad
NDEffGM = record { OM = NDEffOM
                 ; T = TND
                 ; η = ηND
                 ; lift = λ {e} {e'} → liftND e e'
                 ; sub = subND
                 ; sub-mon = subND-mon
                 ; sub-refl = λ {e} → subND-refl {e}
                 ; sub-trans = subND-trans
                 ; mlaw1 = λ {e} → mlaw1ND {e}
                 ; mlaw2 = λ {e} → mlaw2ND {e}
                 ; mlaw3 = λ {e} {e'} {e''} → mlaw3ND e e' e''
                 }




