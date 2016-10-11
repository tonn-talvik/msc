module FinNonDeterminism where

open import Relation.Binary.PropositionalEquality hiding (inspect ; [_])

open import Data.Product
open import Data.List
open import Relation.Nullary
open import Data.Empty
open import Data.Unit

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

-- a.k.a squash ∥_∥
truncate : {P : Set} → Dec P → Set
truncate (yes _) = ⊤
truncate (no  _) = ⊥

-- ∥-∥-yes
extract : {P : Set} → {d : Dec P} → truncate d → P
extract {_} {yes p} t = p
extract {_} {no ¬p} ()

data solveMonND (M N M' N' : ND) : Set where
  mon : M ⊑ND M' → N ⊑ND N' → {_ : truncate ((M ⊙ N) ?⊑ND (M' ⊙ N'))} → solveMonND M N M' N'

solveMonND2monND : {m n m' n' : ND} → (sm : solveMonND m n m' n') → (m ⊙ n) ⊑ND (m' ⊙ n')
solveMonND2monND (mon p q {t}) = extract t

-- FIXME: this does not solve meta-variables
monND : {m n m' n' : ND} → m ⊑ND m' → n ⊑ND n' → (m ⊙ n) ⊑ND (m' ⊙ n')
monND p q = solveMonND2monND (mon p q)

rund = λ {m} → ruND m
assnd = λ {m} {n} {o} → assND m n o

NDEffOM : OrderedMonoid
NDEffOM = record { M = ND
                 ; _⊑_ = _⊑ND_
                 ; reflM = reflND
                 ; transM = transND
                 ; i = nd1
                 ; _·_ = _⊙_ -- \odot ⊙
                 ; mon = monND
                 ; lu = refl
                 ; ru = rund
                 ; ass = λ {m} {n} {o} → assnd {m} {n} {o}
                 }




open import Data.Maybe
--open import Data.BoundedVec renaming (_∷_ to _∷b_; [] to []b )

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

-- is this too precise considering the definition of _⊙_ ?
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

sub-transND : {e e' e'' : ND} {X : Set} →
              (p : e ⊑ND e') → (q : e' ⊑ND e'') → (c : TND e X) → 
              subND q (subND p c) ≡ subND (transND p q) c
sub-transND reflND q c = refl
sub-transND top reflND c = refl
sub-transND top top c = refl
sub-transND 0⊑01 reflND c = refl
sub-transND 0⊑01 top c = refl
sub-transND 1⊑01 reflND c = refl
sub-transND 1⊑01 top c = refl
sub-transND 1⊑1+ reflND c = refl
sub-transND 1⊑1+ top c = refl


mlaw1ND : {e : ND} → {X Y : Set} → (f : X → TND e Y) → (x : X) →
          liftND {nd1} {e} f (ηND x) ≡ f x
mlaw1ND f x = refl


sub-eqND : {e e' : ND} {X : Set} → e ≡ e' → TND e X → TND e' X
sub-eqND = subeq {ND} {TND}


lemma-η-nd1+ : {X : Set} → (c : TND nd1+ X) → sub-eqND {nd1+} rund c ≡ liftND {nd1+} {nd1} ηND c
lemma-η-nd1+ [] = refl
lemma-η-nd1+ (x ∷ c) = cong (_∷_ x) (lemma-η-nd1+ c)


lemma-η-ndN : {X : Set} → (c : TND ndN X) → sub-eqND {ndN} rund c ≡ liftND {ndN} {nd1} ηND c
lemma-η-ndN [] = refl
lemma-η-ndN (x ∷ c) = cong (_∷_ x) (lemma-η-ndN c)


mlaw2ND : {e : ND} → {X : Set} → (c : TND e X) →
          sub-eqND {e} rund c ≡ liftND {e} {nd1} ηND c
mlaw2ND {nd0}  c = refl
mlaw2ND {nd01} (just x) = refl
mlaw2ND {nd01} nothing = refl
mlaw2ND {nd1}  c = refl
mlaw2ND {nd1+} c = lemma-η-nd1+ c
mlaw2ND {ndN}  c = lemma-η-ndN c


{-
lemma-lift : sub-eqND assnd (liftND g (liftND f c))
             ≡ liftND (λ x → liftND g (f x)) c
-}             
mlaw3ND : {e e' e'' : ND} → {X Y Z : Set} →
          (f : X → TND e' Y) → (g : Y → TND e'' Z) → (c : TND e X) → 
          sub-eqND {(e ⊙ e') ⊙ e''} {e ⊙ (e' ⊙ e'')}
                   (assnd {e} {e'} {e''})
                   (liftND {e ⊙ e'} {e''} g (liftND {e} {e'} f c))
          ≡ liftND {e} {e' ⊙ e''} (λ x → liftND {e'} {e''} g (f x)) c
mlaw3ND {nd0} f g c = refl
mlaw3ND {nd01} {nd0} f g c = refl
mlaw3ND {nd01} {nd01} {nd0} f g c = refl
mlaw3ND {nd01} {nd01} {nd01} f g (just x) = refl
mlaw3ND {nd01} {nd01} {nd01} f g nothing = refl
mlaw3ND {nd01} {nd01} {nd1} f g c = {!!}
mlaw3ND {nd01} {nd01} {nd1+} f g c = {!!}
mlaw3ND {nd01} {nd01} {ndN} f g c = {!!}
mlaw3ND {nd01} {nd1} f g c = {!!}
mlaw3ND {nd01} {nd1+} f g c = {!!}
mlaw3ND {nd01} {ndN} f g c = {!!}
mlaw3ND {nd1} f g c = {!!}
mlaw3ND {nd1+} f g c = {!!}
mlaw3ND {ndN} f g c = {!!}          



NDEffGM : GradedMonad
NDEffGM = record { OM = NDEffOM
                 ; T = TND
                 ; η = ηND
                 ; lift = λ {e} {e'} → liftND {e} {e'}
                 ; sub = subND
                 ; sub-mon = {!!}
                 ; sub-refl = λ {e} → sub-reflND {e} -- auto-solve: λ {e} {X} c → refl
                 ; sub-trans = sub-transND
                 ; mlaw1 = λ {e} → mlaw1ND {e}
                 ; mlaw2 = λ {e} → mlaw2ND {e}
                 ; mlaw3 = λ {e} {e'} {e''} → mlaw3ND {e} {e'} {e''}
                 }


