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


data _⊑ND_ : ND → ND → Set where
  reflND : {m : ND} → m ⊑ND m
  top : {m : ND} → m ⊑ND ndN
  0⊑01 : nd0 ⊑ND nd01
  1⊑01 : nd1 ⊑ND nd01
  1⊑1+ : nd1 ⊑ND nd1+


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




?∀ND = ?∀ lstblND

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
                                  (m ?⊑ND n) ?→ (n ?⊑ND o) ?→ (m ?⊑ND o)))))

monautom : (m n m' n' : ND) →  m ⊑ND m' → n ⊑ND n' → (m ⊙ n) ⊑ND (m' ⊙ n')
monautom = extract (?∀ND (λ m → 
                      ?∀ND (λ n → 
                        ?∀ND (λ m' → 
                          ?∀ND (λ n' →
                                  (m ?⊑ND m') ?→ (n ?⊑ND n') ?→ ((m ⊙ n) ?⊑ND (m' ⊙ n')) )))))
{-


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



ruND : {m : ND} → m ≡ m ⊙ nd1
ruND {nd0} = refl
ruND {nd01} = refl
ruND {nd1} = refl
ruND {nd1+} = refl
ruND {ndN} = refl

assND : {m n o : ND} → (m ⊙ n) ⊙ o ≡ m ⊙ (n ⊙ o)
assND {nd0} = refl
assND {nd01} {nd0} = refl
assND {nd01} {nd01} {nd0} = refl
assND {nd01} {nd01} {nd01} = refl
assND {nd01} {nd01} {nd1} = refl
assND {nd01} {nd01} {nd1+} = refl
assND {nd01} {nd01} {ndN} = refl
assND {nd01} {nd1} = refl
assND {nd01} {nd1+} {nd0} = refl
assND {nd01} {nd1+} {nd01} = refl
assND {nd01} {nd1+} {nd1} = refl
assND {nd01} {nd1+} {nd1+} = refl
assND {nd01} {nd1+} {ndN} = refl
assND {nd01} {ndN} {nd0} = refl
assND {nd01} {ndN} {nd01} = refl
assND {nd01} {ndN} {nd1} = refl
assND {nd01} {ndN} {nd1+} = refl
assND {nd01} {ndN} {ndN} = refl
assND {nd1} = refl
assND {nd1+} {nd0} = refl
assND {nd1+} {nd01} {nd0} = refl
assND {nd1+} {nd01} {nd01} = refl
assND {nd1+} {nd01} {nd1} = refl
assND {nd1+} {nd01} {nd1+} = refl
assND {nd1+} {nd01} {ndN} = refl
assND {nd1+} {nd1} = refl
assND {nd1+} {nd1+} {nd0} = refl
assND {nd1+} {nd1+} {nd01} = refl
assND {nd1+} {nd1+} {nd1} = refl
assND {nd1+} {nd1+} {nd1+} = refl
assND {nd1+} {nd1+} {ndN} = refl
assND {nd1+} {ndN} {nd0} = refl
assND {nd1+} {ndN} {nd01} = refl
assND {nd1+} {ndN} {nd1} = refl
assND {nd1+} {ndN} {nd1+} = refl
assND {nd1+} {ndN} {ndN} = refl
assND {ndN} {nd0} = refl
assND {ndN} {nd01} {nd0} = refl
assND {ndN} {nd01} {nd01} = refl
assND {ndN} {nd01} {nd1} = refl
assND {ndN} {nd01} {nd1+} = refl
assND {ndN} {nd01} {ndN} = refl
assND {ndN} {nd1} = refl
assND {ndN} {nd1+} {nd0} = refl
assND {ndN} {nd1+} {nd01} = refl
assND {ndN} {nd1+} {nd1} = refl
assND {ndN} {nd1+} {nd1+} = refl
assND {ndN} {nd1+} {ndN} = refl
assND {ndN} {ndN} {nd0} = refl
assND {ndN} {ndN} {nd01} = refl
assND {ndN} {ndN} {nd1} = refl
assND {ndN} {ndN} {nd1+} = refl
assND {ndN} {ndN} {ndN} = refl

monND : {m n m' n' : ND} → m ⊑ND m' → n ⊑ND n' → (m ⊙ n) ⊑ND (m' ⊙ n')
monND {m' = nd0} reflND q = reflND
monND {m' = nd01} {nd0} reflND reflND = reflND
monND {m' = nd01} {nd0} 0⊑01 reflND = reflND
monND {m' = nd01} {nd0} 1⊑01 reflND = reflND
monND {m' = nd01} {nd01} reflND reflND = reflND
monND {m' = nd01} {nd01} reflND 0⊑01 = 0⊑01
monND {m' = nd01} {nd01} reflND 1⊑01 = reflND
monND {m' = nd01} {nd01} 0⊑01 q = 0⊑01
monND {m' = nd01} {nd01} 1⊑01 q = q
monND {m' = nd01} {nd1} reflND reflND = reflND
monND {m' = nd01} {nd1} 0⊑01 reflND = 0⊑01
monND {m' = nd01} {nd1} 1⊑01 reflND = 1⊑01 -- auto: monND p 1⊑01
monND {m' = nd01} {nd1+} reflND reflND = reflND
monND {m' = nd01} {nd1+} reflND 1⊑1+ = 01⊑N
monND {m' = nd01} {nd1+} 0⊑01 q = 0⊑N
monND {m' = nd01} {nd1+} 1⊑01 reflND = 1+⊑N
monND {m' = nd01} {nd1+} 1⊑01 1⊑1+ = 1⊑N
monND {m' = nd01} {ndN} reflND reflND = reflND
monND {m' = nd01} {ndN} reflND 01⊑N = 01⊑N
monND {m' = nd01} {ndN} reflND 1+⊑N = reflND
monND {m' = nd01} {ndN} reflND 0⊑N = 0⊑N
monND {m' = nd01} {ndN} reflND 1⊑N = 01⊑N
monND {m' = nd01} {ndN} 0⊑01 q = 0⊑N
monND {m' = nd01} {ndN} 1⊑01 q = q
monND {m' = nd1} reflND q = q
monND {m' = nd1+} {nd0} reflND reflND = reflND
monND {m' = nd1+} {nd0} 1⊑1+ reflND = reflND
monND {m' = nd1+} {nd01} reflND reflND = reflND
monND {m' = nd1+} {nd01} reflND 0⊑01 = 0⊑N
monND {m' = nd1+} {nd01} reflND 1⊑01 = 1+⊑N
monND {m' = nd1+} {nd01} 1⊑1+ reflND = 01⊑N
monND {m' = nd1+} {nd01} 1⊑1+ 0⊑01 = 0⊑N
monND {m' = nd1+} {nd01} 1⊑1+ 1⊑01 = 1⊑N
monND {m' = nd1+} {nd1} reflND reflND = reflND
monND {m' = nd1+} {nd1} 1⊑1+ reflND = 1⊑1+
monND {m' = nd1+} {nd1+} reflND reflND = reflND
monND {m' = nd1+} {nd1+} reflND 1⊑1+ = reflND
monND {m' = nd1+} {nd1+} 1⊑1+ q = q
monND {m' = nd1+} {ndN} reflND reflND = reflND
monND {m' = nd1+} {ndN} reflND 01⊑N = reflND
monND {m' = nd1+} {ndN} reflND 1+⊑N = 1+⊑N
monND {m' = nd1+} {ndN} reflND 0⊑N = 0⊑N
monND {m' = nd1+} {ndN} reflND 1⊑N = 1+⊑N
monND {m' = nd1+} {ndN} 1⊑1+ q = q
monND {m' = ndN} {nd0} reflND reflND = reflND
monND {m' = ndN} {nd0} 01⊑N reflND = reflND
monND {m' = ndN} {nd0} 1+⊑N reflND = reflND
monND {m' = ndN} {nd0} 0⊑N q = reflND
monND {m' = ndN} {nd0} 1⊑N q = q
monND {m' = ndN} {nd01} reflND reflND = reflND
monND {m' = ndN} {nd01} reflND 0⊑01 = 0⊑N
monND {m' = ndN} {nd01} reflND 1⊑01 = reflND
monND {m' = ndN} {nd01} 01⊑N reflND = 01⊑N
monND {m' = ndN} {nd01} 01⊑N 0⊑01 = 0⊑N
monND {m' = ndN} {nd01} 01⊑N 1⊑01 = 01⊑N
monND {m' = ndN} {nd01} 1+⊑N reflND = reflND
monND {m' = ndN} {nd01} 1+⊑N 0⊑01 = 0⊑N
monND {m' = ndN} {nd01} 1+⊑N 1⊑01 = 1+⊑N
monND {m' = ndN} {nd01} 0⊑N q = 0⊑N
monND {m' = ndN} {nd01} 1⊑N reflND = 01⊑N
monND {m' = ndN} {nd01} 1⊑N 0⊑01 = 0⊑N
monND {m' = ndN} {nd01} 1⊑N 1⊑01 = 1⊑N
monND {m' = ndN} {nd1} reflND reflND = reflND
monND {m' = ndN} {nd1} 01⊑N reflND = 01⊑N
monND {m' = ndN} {nd1} 1+⊑N reflND = 1+⊑N
monND {m' = ndN} {nd1} 0⊑N q = 0⊑N
monND {m' = ndN} {nd1} 1⊑N reflND = 1⊑N
monND {m' = ndN} {nd1+} reflND reflND = reflND
monND {m' = ndN} {nd1+} reflND 1⊑1+ = reflND
monND {m' = ndN} {nd1+} 01⊑N reflND = reflND
monND {m' = ndN} {nd1+} 01⊑N 1⊑1+ = 01⊑N
monND {m' = ndN} {nd1+} 1+⊑N reflND = 1+⊑N
monND {m' = ndN} {nd1+} 1+⊑N 1⊑1+ = 1+⊑N
monND {m' = ndN} {nd1+} 0⊑N q = 0⊑N
monND {m' = ndN} {nd1+} 1⊑N reflND = 1+⊑N
monND {m' = ndN} {nd1+} 1⊑N 1⊑1+ = 1⊑N
monND {m' = ndN} {ndN} reflND reflND = reflND
monND {m' = ndN} {ndN} reflND 01⊑N = reflND
monND {m' = ndN} {ndN} reflND 1+⊑N = reflND
monND {m' = ndN} {ndN} reflND 0⊑N = 0⊑N
monND {m' = ndN} {ndN} reflND 1⊑N = reflND
monND {m' = ndN} {ndN} 01⊑N reflND = reflND
monND {m' = ndN} {ndN} 01⊑N 01⊑N = 01⊑N
monND {m' = ndN} {ndN} 01⊑N 1+⊑N = reflND
monND {m' = ndN} {ndN} 01⊑N 0⊑N = 0⊑N
monND {m' = ndN} {ndN} 01⊑N 1⊑N = 01⊑N
monND {m' = ndN} {ndN} 1+⊑N reflND = reflND
monND {m' = ndN} {ndN} 1+⊑N 01⊑N = reflND
monND {m' = ndN} {ndN} 1+⊑N 1+⊑N = 1+⊑N
monND {m' = ndN} {ndN} 1+⊑N 0⊑N = 0⊑N
monND {m' = ndN} {ndN} 1+⊑N 1⊑N = 1+⊑N
monND {m' = ndN} {ndN} 0⊑N q = 0⊑N
monND {m' = ndN} {ndN} 1⊑N q = q

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

