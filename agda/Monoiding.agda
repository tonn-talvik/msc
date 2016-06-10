{-# OPTIONS --type-in-type #-}

module Monoiding where

open import Relation.Binary.Core using (_≡_ ; refl)

record OrderedMonoid : Set where
  field
    M : Set
 
    _≤M_ : M → M → Set
    reflM : {m : M} → m ≤M m
    transM : {m n o : M} → m ≤M n → n ≤M o → m ≤M o

    i : M 
    _·_ : M → M → M
    lu : { m : M } → i · m ≡ m
    ru : { m : M } → m · i ≡ m
    ass : { m n o : M} → (m · n) · o ≡ m · (n · o)


data E : Set where
  err : E
  ok : E 
  errok : E

data _≤E_ : E → E → Set where
  reflE : {m : E} → m ≤E m
  err≤Eerrok : err ≤E errok
  ok≤Eerrok : ok ≤E errok

transE : {m n o : E} → m ≤E n → n ≤E o → m ≤E o
transE reflE q = q
transE err≤Eerrok reflE =  err≤Eerrok
transE ok≤Eerrok reflE =  ok≤Eerrok

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


ExcEffOM : OrderedMonoid
ExcEffOM = record { M = E 
                  ; _≤M_ = _≤E_ 
                  ; reflM = reflE
                  ; transM = transE
                  ; i = ok
                  ; _·_ = _·E_
                  ; lu =  refl
                  ; ru = ruE 
                  ; ass = {!!}
                  }

