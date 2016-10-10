module NonDeterminism where

open import Relation.Binary.Core using (_≡_ ; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import Function
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
TND nd X = List X  -- powerset? Use BoundedVec instead?

{-
open import Data.Nat
open import Data.BoundedVec renaming (_∷_ to _∷b_; [] to []b )
bv1 bv2 : BoundedVec ℕ 2
bv1 = zero ∷b []b
bv2 = zero ∷b zero ∷b []b
-}


ηND : {X : Set} → X → TND (nd1) X
ηND x = [ x ]

liftND :  (e e' : ND) {X Y : Set} →
      (X → TND e' Y) → TND e X → TND (e ⊙ e') Y
liftND e e' f [] = []
liftND e e' f (x ∷ xs) = (f x) ++ (liftND e e' f xs)

-- Is this correct? Isn't TND too broad?
subND : {e e' : ND} {X : Set} → e ⊑ND e' → TND e X → TND e' X
subND p x = x

sub-reflND : {e : ND} {X : Set} → (c : TND e X) → subND {e} reflND c ≡ c
sub-reflND _ = refl

sub-monND : {e e' e'' e''' : ND} {X Y : Set} →
            (p : e ⊑ND e'') → (q : e' ⊑ND e''') →
            (f : X → TND e' Y) → (c : TND e X) → 
            subND (monND p q) (liftND e e' f c) ≡ liftND e'' e''' (subND q ∘ f) (subND p c)
sub-monND p q f c = refl



sub-transND : {e e' e'' : ND} {X : Set} →
              (p : e ⊑ND e') → (q : e' ⊑ND e'') → (c : TND e X) → 
              subND q (subND p c) ≡ subND (transND p q) c
sub-transND r q c = refl


++-right-identity : {X : Set} (xs : List X) → xs ++ [] ≡ xs
++-right-identity [] = refl
++-right-identity (x ∷ xs) = cong (_∷_ x) (++-right-identity xs)

mlaw1ND : {e : ND} → {X Y : Set} → (f : X → TND e Y) → (x : X) →
          liftND nd1 e f (ηND x) ≡ f x
mlaw1ND f x = ++-right-identity (f x)



sub-eqND : {e e' : ND} {X : Set} → e ≡ e' → TND e X → TND e' X
sub-eqND = subeq {ND} {TND}


η-lift-identity : {e e' : ND} {X : Set} (xs : List X) → xs ≡ liftND e e' ηND xs
η-lift-identity [] = refl
η-lift-identity {e} {e'} (x ∷ xs) = cong (_∷_ x) (η-lift-identity {e} {e'} xs)

mlaw2ND :  {e : ND} → {X : Set} → (c : TND e X) →
           sub-eqND {e} ruND c ≡ liftND e nd1 ηND c
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


-- this is not needed anymore?
what : {e e' e'' : ND} {X : Set} → sub-eqND {(e ⊙ e') ⊙ e''} {e ⊙ (e' ⊙ e'')} {X}
                                   (assND {e} {e'} {e''}) []
                          ≡ []
what {nd0} = refl
what {nd01} {nd0} = refl
what {nd01} {nd01} {nd0} = refl
what {nd01} {nd01} {nd01} = refl
what {nd01} {nd01} {nd1} = refl
what {nd01} {nd01} {nd1+} = refl
what {nd01} {nd01} {ndN} = refl
what {nd01} {nd1} = refl
what {nd01} {nd1+} {nd0} = refl
what {nd01} {nd1+} {nd01} = refl
what {nd01} {nd1+} {nd1} = refl
what {nd01} {nd1+} {nd1+} = refl
what {nd01} {nd1+} {ndN} = refl
what {nd01} {ndN} {nd0} = refl
what {nd01} {ndN} {nd01} = refl
what {nd01} {ndN} {nd1} = refl
what {nd01} {ndN} {nd1+} = refl
what {nd01} {ndN} {ndN} = refl
what {nd1} = refl
what {nd1+} {nd0} = refl
what {nd1+} {nd01} {nd0} = refl
what {nd1+} {nd01} {nd01} = refl
what {nd1+} {nd01} {nd1} = refl
what {nd1+} {nd01} {nd1+} = refl
what {nd1+} {nd01} {ndN} = refl
what {nd1+} {nd1} = refl
what {nd1+} {nd1+} {nd0} = refl
what {nd1+} {nd1+} {nd01} = refl
what {nd1+} {nd1+} {nd1} = refl
what {nd1+} {nd1+} {nd1+} = refl
what {nd1+} {nd1+} {ndN} = refl
what {nd1+} {ndN} {nd0} = refl
what {nd1+} {ndN} {nd01} = refl
what {nd1+} {ndN} {nd1} = refl
what {nd1+} {ndN} {nd1+} = refl
what {nd1+} {ndN} {ndN} = refl
what {ndN} {nd0} = refl
what {ndN} {nd01} {nd0} = refl
what {ndN} {nd01} {nd01} = refl
what {ndN} {nd01} {nd1} = refl
what {ndN} {nd01} {nd1+} = refl
what {ndN} {nd01} {ndN} = refl
what {ndN} {nd1} = refl
what {ndN} {nd1+} {nd0} = refl
what {ndN} {nd1+} {nd01} = refl
what {ndN} {nd1+} {nd1} = refl
what {ndN} {nd1+} {nd1+} = refl
what {ndN} {nd1+} {ndN} = refl
what {ndN} {ndN} {nd0} = refl
what {ndN} {ndN} {nd01} = refl
what {ndN} {ndN} {nd1} = refl
what {ndN} {ndN} {nd1+} = refl
what {ndN} {ndN} {ndN} = refl


mlaw3ND : {e e' e'' : ND} → {X Y Z : Set} →
          (f : X → TND e' Y) → (g : Y → TND e'' Z) → (c : TND e X) → 
          sub-eqND {(e ⊙ e') ⊙ e''} {e ⊙ (e' ⊙ e'')}
                   (assND {e} {e'} {e''})
                   (liftND (e ⊙ e') e'' g (liftND e e' f c))
          ≡ liftND (e) (e' ⊙ e'') (λ x → liftND e' e'' g (f x)) c
mlaw3ND {e} {e'} {e''} f g [] = what {e} {e'} {e''}
mlaw3ND {e} {e'} {e''} f g (x ∷ c) = {!!}

--mlaw3ND {e} {e'} {e''} f g [] = what {e} {e'} {e''}
--mlaw3ND {e} {e'} {e''} f g (x ∷ c) = subeq refl liftND --cong (_++_ {!!}) refl
--mlaw3ND {e} {e'} {e''} f g (x ∷ c) with liftND {e ⊙ e'} {e''} g (liftND {e} {e'} f c)
--... | fx = cong ((concatMap (liftND {e'} {e''} g))) refl
--... | l = cong (concatMap (liftND {e} {e' ⊙ e''} ((liftND {e'} {e''} g) ∘ f))) refl

{-
-- this is wrong
mlaw3ND {e} {e'} {e''} f g c with liftND {e ⊙ e'} {e''} g (liftND {e} {e'} f c)
... | l = cong (λ cs → concatMap g cs) {{!!}} refl
-}


NDEffGM : GradedMonad
NDEffGM = record { OM = NDEffOM
                 ; T = TND
                 ; η = ηND
                 ; lift = λ {e} {e'} → liftND e e'
                 ; sub = subND
                 ; sub-mon = sub-monND
                 ; sub-refl = λ {e} → sub-reflND {e}
                 ; sub-trans = sub-transND
                 ; mlaw1 = λ {e} → mlaw1ND {e}
                 ; mlaw2 = λ {e} → mlaw2ND {e}
                 ; mlaw3 = λ {e} {e'} {e''} → mlaw3ND {e} {e'} {e''}
                 }
