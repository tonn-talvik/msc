module FinNonDeterminism where

open import Relation.Binary.PropositionalEquality hiding (inspect)

open import Data.Product
open import Data.List

------------------------------------------------------
-- Paper from http://cs.ioc.ee/~denis/finset/
-- Code from  http://cs.ioc.ee/~denis/phd/code.zip

open import Fin.FiniteSubset
open import Fin.Finiteness
open import Fin.Prover
open import Utils.ListProperties 
  using (_∈_ ; here ; there)
open import Utils.Logic

-------------------------------------------------------

open import OrderedMonoid
open import GradedMonad

data ND : Set where
  nd0  : ND
  nd01 : ND
  nd1  : ND
  nd1+ : ND
  ndN  : ND


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

listND : List ND
listND = nd0 ∷ nd01 ∷ nd1 ∷ nd1+ ∷ ndN ∷ [] 

cmpltND : (x : ND) → x ∈ listND
cmpltND nd0 = here
cmpltND nd01 = there here
cmpltND nd1 = there (there here)
cmpltND nd1+ = there (there (there here))
cmpltND ndN = there (there (there (there here)))

NDListbl : Listable ND
NDListbl = listND , cmpltND

-----------------------------------------------------------

_?nd=_ : DecEq ND
_?nd=_ = lstblEq NDListbl


ruND : (m : ND) → m ≡ m ⊙ nd1
ruND = ∥-∥-yes (Π m ∈ NDListbl ∙ (m ?nd= (m ⊙ nd1)))

assND : (m n o : ND) → (m ⊙ n) ⊙ o ≡ m ⊙ (n ⊙ o)
assND = ∥-∥-yes (Π m ∈ NDListbl ∙
                   Π n ∈ NDListbl ∙
                   Π o ∈ NDListbl ∙
                   ( ((m ⊙ n) ⊙ o) ?nd= (m ⊙ (n ⊙ o)) ))


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

