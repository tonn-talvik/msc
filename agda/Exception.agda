module Exception where

open import Relation.Binary.Core using (_≡_ ; refl)
open import OrderedMonoid 
open import GradedMonad

data E : Set where
  err : E
  ok : E 
  errok : E

data _⊑E_ : E → E → Set where
  reflE : {m : E} → m ⊑E m
  err⊑Eerrok : err ⊑E errok
  ok⊑Eerrok : ok ⊑E errok

transE : {m n o : E} → m ⊑E n → n ⊑E o → m ⊑E o
transE reflE q = q
transE err⊑Eerrok reflE = err⊑Eerrok
transE ok⊑Eerrok reflE = ok⊑Eerrok

_·E_ : E → E → E
ok ·E m = m
err ·E m = err
errok ·E err = err
errok ·E ok = errok
errok ·E errok = errok

ruE : {m : E} →  m ≡ m ·E ok 
ruE {err} = refl
ruE {ok} = refl
ruE {errok} = refl

assE : {m n o : E} → (m ·E n) ·E o ≡ m ·E (n ·E o)
assE {err} = refl
assE {ok} = refl
assE {errok} {err} = refl
assE {errok} {ok} = refl
assE {errok} {errok} {err} = refl
assE {errok} {errok} {ok} = refl
assE {errok} {errok} {errok} = refl


monE : {m n m' n' : E} → m ⊑E m' → n ⊑E n' → (m ·E n) ⊑E (m' ·E n')
monE {m' = err} reflE q = reflE
monE {m' = ok} reflE q = q
monE {m' = errok} {err} reflE reflE = reflE
monE {m' = errok} {err} err⊑Eerrok reflE = reflE
monE {m' = errok} {err} ok⊑Eerrok reflE = reflE
monE {m' = errok} {ok} reflE reflE = reflE
monE {m' = errok} {ok} err⊑Eerrok reflE = err⊑Eerrok
monE {m' = errok} {ok} ok⊑Eerrok reflE = ok⊑Eerrok
monE {m' = errok} {errok} reflE reflE = reflE
monE {m' = errok} {errok} reflE err⊑Eerrok = err⊑Eerrok
monE {m' = errok} {errok} reflE ok⊑Eerrok = reflE
monE {m' = errok} {errok} err⊑Eerrok q = err⊑Eerrok
monE {m' = errok} {errok} ok⊑Eerrok reflE = reflE
monE {m' = errok} {errok} ok⊑Eerrok err⊑Eerrok = err⊑Eerrok
monE {m' = errok} {errok} ok⊑Eerrok ok⊑Eerrok = ok⊑Eerrok


ExcEffOM : OrderedMonoid
ExcEffOM = record { M = E 
                  ; _⊑_ = _⊑E_ 
                  ; reflM = reflE
                  ; transM = transE
                  ; i = ok
                  ; _·_ = _·E_
                  ; mon = monE
                  ; lu = refl
                  ; ru = ruE 
                  ; ass = λ {m} {n} {o} → assE {m} {n} {o}
                  }

open import Data.Unit
open import Data.Maybe

TE : E → Set → Set
TE err X = ⊤
TE ok X = X
TE errok X = Maybe X

ηE : {X : Set} → X → X
ηE x = x

open OrderedMonoid.OrderedMonoid
liftE : {e e' : E} {X Y : Set} →
      (X → TE e' Y) → TE e X → TE (e ·E e') Y
liftE {err} f x = tt
liftE {ok} f x = f x
liftE {errok} {err} f (just x) = tt
liftE {errok} {ok} f (just x) = just (f x)
liftE {errok} {errok} f (just x) = f x
liftE {errok} {err} f nothing = tt
liftE {errok} {ok} f nothing = nothing
liftE {errok} {errok} f nothing = nothing


ExcEffGM : GradedMonad
ExcEffGM = record { OM = ExcEffOM
                  ; T = TE
                  ; η = ηE
                  ; lift = λ {e} {e'} → liftE {e} {e'}
                  ; sub = {!!}
                  ; submon = {!!}
                  ; subrefl = {!!}
                  ; subtrans = {!!}
                  ; mlaw1 = {!!}
                  ; mlaw2 = {!!}
                  ; mlaw3 = {!!}
                  }
