module NonDeterminism where

open import Function
open import Data.List
open import Relation.Nullary


open import Relation.Binary.Core using (_≡_ ; refl)
open import Relation.Binary.PropositionalEquality using (cong)

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


{-
open import Data.Nat
open import Data.Vec

-- FIXME: yellow submarine
tail-≡ : {X : Set} {x x' : X} {n : ℕ} {xs xs' : Vec X n} → (x ∷ xs ≡ x' ∷ xs') → xs ≡ xs'
tail-≡ p = cong tail refl

head-≡ : {X : Set} {x x' : X} {n : ℕ} {xs xs' : Vec X n} → (x ∷ xs ≡ x' ∷ xs') → x ≡ x'
head-≡ p = cong head refl


_?≡vec_ : {X : Set} {n : ℕ} (xs xs' : Vec X n) → {_ : DecEq X} → Dec (xs ≡ xs')
[] ?≡vec [] = yes refl
((x ∷ xs) ?≡vec (x' ∷ xs')) {eq} with eq x x'
((x ∷ xs) ?≡vec (x' ∷ xs')) {eq} | yes p with (xs ?≡vec xs') {eq}
(x ∷ xs) ?≡vec (x' ∷ xs') | yes p | yes q rewrite p | q = yes refl
(x ∷ xs) ?≡vec (x' ∷ xs') | yes p | no ¬q rewrite p = no (λ ys → ¬q (tail-≡ ys))
(x ∷ xs) ?≡vec (x' ∷ xs') | no ¬p = no (λ ys → ¬p (head-≡ ys))
-}

{-
_?≡list_ : {X : Set} (xs xs' : List X) → {_ : DecEq X} → Dec (xs ≡ xs')
[] ?≡list [] = yes refl
[] ?≡list (_ ∷ _) = no (λ ())
(_ ∷ _) ?≡list [] = no (λ ())
((x ∷ xs) ?≡list (x' ∷ xs')) {eq} with eq x x'
((x ∷ xs) ?≡list (x' ∷ xs')) {eq} | yes p with (xs ?≡list xs') {eq}
(x ∷ xs) ?≡list (x' ∷ xs') | yes p | yes q rewrite p | q = yes refl
(x ∷ xs) ?≡list (x' ∷ xs') | yes p | no ¬q rewrite p = no (λ x₁ → {!!})
(x ∷ xs) ?≡list (x' ∷ xs') | no ¬p = no (λ xx → {!!})
-}

{-
decVecEq2decListEq : {X : Set} {n : ℕ} {xs xs' : Vec X n} → Dec (xs ≡ xs') → Dec (toList xs ≡ toList xs')
decVecEq2decListEq (yes p) rewrite p = yes (cong toList refl)
decVecEq2decListEq (no ¬p) = no (λ q → ¬p {!!})

-- FIXME: yellow

_?≡list_ : {X : Set} (xs xs' : List X) → {_ : DecEq X} → Dec (xs ≡ xs')
xs ?≡list xs' = decVecEq2decListEq (fromList {!!} ?≡vec fromList {!!})


?Empty : {X : Set} (l : List X) → Dec (l ≡ [])
?Empty [] = yes refl
?Empty (x ∷ l) = no (λ ())
what : {X : Set} (e e' e'' : ND) → subND-eq {(e ⊙ e') ⊙ e''} {e ⊙ (e' ⊙ e'')} {X}
                                   (ass-⊙ e e' e'') []
                          ≡ []
what = extract (?∀ND (λ e →
                  ?∀ND (λ e' →
                    ?∀ND (λ e'' → ?Empty
                      (subND-eq {(e ⊙ e') ⊙ e''} {e ⊙ (e' ⊙ e'')}
                               (ass-⊙ e e' e'') [])))))


mlaw3ND : (e e' e'' : ND) → {X Y Z : Set} →
          (f : X → TND e' Y) → (g : Y → TND e'' Z) → (c : TND e X) → 
          subND-eq {(e ⊙ e') ⊙ e''} {e ⊙ (e' ⊙ e'')}
                   (ass-⊙ e e' e'')
                   (liftND (e ⊙ e') e'' g (liftND e e' f c))
          ≡ liftND e (e' ⊙ e'') (λ x → liftND e' e'' g (f x)) c
--          ≡ liftND e (e' ⊙ e'') (liftND e' e'' g ∘ f) c
mlaw3ND e e' e'' f g [] = what e e' e''
mlaw3ND e e' e'' f g (c ∷ cs) = {!!}
-}

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
--                 ; mlaw3 = λ {e} {e'} {e''} → mlaw3ND e e' e''
                 }




