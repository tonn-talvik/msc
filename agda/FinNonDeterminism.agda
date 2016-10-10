module FinNonDeterminism where

open import Relation.Binary.PropositionalEquality hiding (inspect ; [_])

open import Data.Product
open import Data.List
open import Relation.Nullary

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

-----------------------------------------------------------

data _⊑ND_ : ND → ND → Set where
  reflND : {m : ND} → m ⊑ND m
  top : {m : ND} → m ⊑ND ndN
  0⊑01 : nd0 ⊑ND nd01
  1⊑01 : nd1 ⊑ND nd01
  1⊑1+ : nd1 ⊑ND nd1+


transND : {m n o : ND} → m ⊑ND n → n ⊑ND o → m ⊑ND o
transND reflND q = q
transND _ top = top
transND p reflND = p

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

monND : {m n m' n' : ND} → m ⊑ND m' → n ⊑ND n' → (m ⊙ n) ⊑ND (m' ⊙ n')
monND = {!!}


NDEffOM : OrderedMonoid
NDEffOM = record { M = ND
                 ; _⊑_ = _⊑ND_
                 ; reflM = reflND
                 ; transM = transND
                 ; i = nd1
                 ; _·_ = _⊙_ -- \odot ⊙
                 ; mon = monND
                 ; lu = refl
                 ; ru = λ {m} → ruND m
                 ; ass = λ {m} {n} {o} → assND m n o
                 }



open import Data.Unit
open import Data.Maybe
open import Data.BoundedVec renaming (_∷_ to _∷b_; [] to []b )

TND : ND → Set → Set
TND nd0  X = ⊤
TND nd01 X = Maybe X
TND nd1  X = X
TND nd1+ X = List X -- ? lower bounded vec
TND ndN  X = List X

ηND : {X : Set} → X → TND (nd1) X
ηND x = x

maybe-to-list : {X : Set} → Maybe X → List X
maybe-to-list (just x) = [ x ]
maybe-to-list nothing = []

liftND :  {e e' : ND} {X Y : Set} →
      (X → TND e' Y) → TND e X → TND (e ⊙ e') Y
liftND {nd0}  f x = tt
liftND {nd01} {nd0} f x = tt
-- bind??? (Data.Maybe.monad {level})._>>=_ 
liftND {nd01} {nd01} f (just x) = f x
liftND {nd01} {nd01} f nothing = nothing 
liftND {nd01} {nd1} f x = Data.Maybe.map f x
liftND {nd01} {nd1+} f (just x) = f x
liftND {nd01} {nd1+} f nothing = []
liftND {nd01} {ndN} f (just x) = f x
liftND {nd01} {ndN} f nothing = []
liftND {nd1}  f x = f x
-- "Absurd"??? But see liftND {nd1+} {nd1} f (x ∷ xs)
liftND {nd1+} {nd0} f [] = tt
liftND {nd1+} {nd01} f [] = []
liftND {nd1+} {nd1} f [] = []
liftND {nd1+} {nd1+} f [] = []
liftND {nd1+} {ndN} f [] = []  
liftND {nd1+} {nd0} f (x ∷ xs) = tt
liftND {nd1+} {nd01} f (x ∷ xs) = maybe-to-list (f x) ++ liftND {nd1+} {nd01} f xs
liftND {nd1+} {nd1} f (x ∷ xs) = f x ∷ liftND {nd1+} {nd1} f xs
liftND {nd1+} {nd1+} f (x ∷ xs) = f x ++ liftND {nd1+} {nd1+} f xs
liftND {nd1+} {ndN} f (x ∷ xs) = f x ++ liftND {nd1+} {ndN} f xs
liftND {ndN} {nd0} f [] = tt
liftND {ndN} {nd01} f [] = []
liftND {ndN} {nd1} f [] = []
liftND {ndN} {nd1+} f [] = []
liftND {ndN} {ndN} f [] = []
liftND {ndN} {nd0} f (x ∷ xs) = tt
liftND {ndN} {nd01} f (x ∷ xs) = maybe-to-list (f x) ++ liftND {ndN} {nd01} f xs
liftND {ndN} {nd1} f (x ∷ xs) = f x ∷ liftND {ndN} {nd1} f xs
liftND {ndN} {nd1+} f (x ∷ xs) = f x ++ liftND {ndN} {nd1+} f xs
liftND {ndN} {ndN} f (x ∷ xs) = f x ++ liftND {ndN} {ndN} f xs
{-
liftND f [] = []
liftND {e} {e'} f (x ∷ xs) = (f x) ++ (liftND {e} {e'} f xs)
-}

subND : {e e' : ND} {X : Set} → e ⊑ND e' → TND e X → TND e' X
subND reflND x = x
subND {nd0} top x = []
subND {nd01} top x = maybe-to-list x
subND {nd1} top x = [ x ]
subND {nd1+} top x = x
subND {ndN} top x = x
-- How does auto-solve solve these? Maybe constructor definition order?
subND 0⊑01 x = nothing
subND 1⊑01 x = just x
subND 1⊑1+ x = [ x ]

sub-reflND : {e : ND} {X : Set} → (c : TND e X) → subND {e} reflND c ≡ c
sub-reflND _ = refl

NDEffGM : GradedMonad
NDEffGM = record { OM = NDEffOM
                 ; T = TND
                 ; η = ηND
                 ; lift = λ {e} {e'} → liftND {e} {e'}
                 ; sub = subND
                 ; sub-mon = {!!}
                 ; sub-refl = λ {e} → sub-reflND {e} -- auto-solve: λ {e} {X} c → refl
                 ; sub-trans = {!!}
                 ; mlaw1 = {!!}
                 ; mlaw2 = {!!}
                 ; mlaw3 = {!!}
                 }



