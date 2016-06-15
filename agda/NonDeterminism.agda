module NonDeterminism where

open import Relation.Binary.Core using (_≡_ ; refl)
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
  0⊑01 : nd0 ⊑ND nd01
  1⊑01 : nd1 ⊑ND nd01
  1⊑1+ : nd1 ⊑ND nd1+
  01⊑N : nd01 ⊑ND ndN
  1+⊑N : nd1+ ⊑ND ndN
  -- 0⊑N, 1⊑N are needed?
  0⊑N : nd0 ⊑ND ndN
  1⊑N : nd1 ⊑ND ndN

transND : {m n o : ND} → m ⊑ND n → n ⊑ND o → m ⊑ND o
transND reflND q = q
transND 0⊑01 reflND = 0⊑01
transND 0⊑01 01⊑N = 0⊑N
transND 1⊑01 reflND = 1⊑01
transND 1⊑01 01⊑N = 1⊑N
transND 1⊑1+ reflND = 1⊑1+
transND 1⊑1+ 1+⊑N = 1⊑N
transND 01⊑N reflND = 01⊑N
transND 1+⊑N reflND = 1+⊑N
transND 0⊑N reflND = 0⊑N
transND 1⊑N reflND = 1⊑N

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



ruND : {m : ND} → m ⊙ nd1 ≡ m
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

NDEffOM : OrderedMonoid
NDEffOM = record { M = ND
                 ; _⊑_ = _⊑ND_
                 ; reflM = reflND
                 ; transM = transND
                 ; i = nd1
                 ; _·_ = _⊙_
                 ; lu = refl
                 ; ru = ruND
                 ; ass = assND
                 }

open import Data.List

TND : ND → Set → Set
TND nd X = List X  -- powerset?

ηND : {X : Set} → X → TND (nd1) X
ηND x = [ x ]

liftND :  {e e' : ND} {X Y : Set} →
      (X → TND e' Y) → TND e X → TND (e ⊙ e') Y
liftND f [] = []
liftND f (x ∷ xs) = (f x) ++ (liftND f xs)


NDEffGM : GradedMonad
NDEffGM = record { OM = NDEffOM
                 ; T = TND
                 ; η = ηND
                 ; lift = liftND
                 }
