module NonDeterminism-try where


open import Data.List
open import Relation.Nullary


open import Relation.Binary.Core using (_≡_ ; refl)
--open import OrderedMonoid
--open import GradedMonad

open import Finiteness


data ND : Set where
  nd0  : ND
  nd01 : ND
  nd1  : ND
  nd1+ : ND
  ndN  : ND

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


data _⊑ND_ : ND → ND → Set where
  reflND : {m : ND} → m ⊑ND m
  top : {m : ND} → m ⊑ND ndN
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




_?⊑ND_ : (m : ND) → (n : ND) → Dec (m ⊑ND n)
nd0 ?⊑ND nd0 = yes reflND
nd0 ?⊑ND nd01 = yes 0⊑01
nd0 ?⊑ND nd1 = no (λ ())
nd0 ?⊑ND nd1+ = no (λ ())
nd0 ?⊑ND ndN = yes top
nd01 ?⊑ND nd0 = no (λ ())
nd01 ?⊑ND nd01 = yes reflND
nd01 ?⊑ND nd1 = no (λ ())
nd01 ?⊑ND nd1+ = no (λ ())
nd01 ?⊑ND ndN = yes top
nd1 ?⊑ND nd0 = no (λ ())
nd1 ?⊑ND nd01 = yes 1⊑01
nd1 ?⊑ND nd1 = yes reflND
nd1 ?⊑ND nd1+ = yes 1⊑1+
nd1 ?⊑ND ndN = yes top
nd1+ ?⊑ND nd0 = no (λ ())
nd1+ ?⊑ND nd01 = no (λ ())
nd1+ ?⊑ND nd1 = no (λ ())
nd1+ ?⊑ND nd1+ = yes reflND
nd1+ ?⊑ND ndN = yes top
ndN ?⊑ND nd0 = no (λ ())
ndN ?⊑ND nd01 = no (λ ())
ndN ?⊑ND nd1 = no (λ ())
ndN ?⊑ND nd1+ = no (λ ())
ndN ?⊑ND ndN = yes reflND 




reflautom : (m : ND) → m  ⊑ND m
reflautom = extract (?∀ND (λ m → m ?⊑ND m))

-- transitivity manually
transND : {m n o : ND} → m ⊑ND n → n ⊑ND o → m ⊑ND o
transND reflND q = q
transND p top = top
transND p reflND = p

-- transitivity automatically using typechecker
transautom : (m n o : ND) → m ⊑ND n → n ⊑ND o → m ⊑ND o
transautom = extract (?∀ND (λ m → 
                          ?∀ND (λ n → 
                             ?∀ND (λ o →   
                                  (m ?⊑ND n) ?→ ((n ?⊑ND o) ?→ (m ?⊑ND o))))))

ruND : {m : ND} → m ≡ m ⊙ nd1
ruND {nd0} = refl
ruND {nd01} = refl
ruND {nd1} = refl
ruND {nd1+} = refl
ruND {ndN} = refl

ruNDautom : (m : ND) → m ≡ m ⊙ nd1
ruNDautom = extract (?∀ND (λ m → m ?≡ND m  ⊙ nd1))


monautom : (m n m' n' : ND) →  m ⊑ND m' → n ⊑ND n' → (m ⊙ n) ⊑ND (m' ⊙ n')
monautom = extract (?∀ND (λ m → 
                      ?∀ND (λ n → 
                        ?∀ND (λ m' → 
                          ?∀ND (λ n' →
                                  (m ?⊑ND m') ?→ ((n ?⊑ND n') ?→ ((m ⊙ n) ?⊑ND (m' ⊙ n'))) )))))
                                  
assNDautom : (m n o : ND) → (m ⊙ n) ⊙ o ≡ m ⊙ (n ⊙ o)
assNDautom = extract (?∀ND (λ m → 
                        ?∀ND (λ n → 
                          ?∀ND (λ o →
                            ((m ⊙ n) ⊙ o) ?≡ND (m ⊙ (n ⊙ o)) ))))
{-

NDEffOM : OrderedMonoid
NDEffOM = record { M = ND
                 ; _⊑_ = _⊑ND_
                 ; reflM = reflND
                 ; transM = transND
                 ; i = nd1
                 ; _·_ = _⊙_ -- \odot ⊙
                 ; mon = monND
                 ; lu = refl
                 ; ru = ruND
                 ; ass = λ {m} {n} {o} → assND {m} {n} {o}
                 }

open import Data.List

TND : ND → Set → Set
TND nd X = List X  -- powerset?

ηND : {X : Set} → X → TND (nd1) X
ηND x = [ x ]

liftND :  {e e' : ND} {X Y : Set} →
      (X → TND e' Y) → TND e X → TND (e ⊙ e') Y
liftND f [] = []
liftND {e} {e'} f (x ∷ xs) = (f x) ++ (liftND {e} {e'} f xs)


NDEffGM : GradedMonad
NDEffGM = record { OM = NDEffOM
                 ; T = TND
                 ; η = ηND
                 ; lift = λ {e} {e'} → liftND {e} {e'}
                 ; sub = {!!}
                 ; sub-mon = {!!}
                 ; sub-eq = {!!}
                 ; sub-refl = {!!}
                 ; sub-trans = {!!}
                 ; mlaw1 = {!!}
                 ; mlaw2 = {!!}
                 ; mlaw3 = {!!}
                 }

-}

