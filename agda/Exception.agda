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

ruE : {m : E} →  m ·E ok ≡ m
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


ExcEffOM : OrderedMonoid
ExcEffOM = record { M = E 
                  ; _⊑_ = _⊑E_ 
                  ; reflM = reflE
                  ; transM = transE
                  ; i = ok
                  ; _·_ = _·E_
                  ; lu = refl
                  ; ru = ruE 
                  ; ass = assE
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
                  ; lift = liftE
                  }
