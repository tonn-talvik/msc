module Exception where

open import Relation.Binary.Core using (_≡_ ; refl)
open import Function
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

ruE : {e : E} →  e ≡ e ·E ok 
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

ηE : {X : Set} → X → TE ok X
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

subE : {e e' : E} {X : Set} → e ⊑E e' → TE e X → TE e' X
subE reflE x = x
subE err⊑Eerrok x = nothing
subE ok⊑Eerrok x = just x


sub-reflE : {e : E} {X : Set} → (c : TE e X) → subE {e} reflE c ≡ c
sub-reflE _ = refl

sub-monE : {e e' e'' e''' : E} {X Y : Set} →
           (p : e ⊑E e'') → (q : e' ⊑E e''') →
           (f : X → TE e' Y) → (c : TE e X) → 
           subE (monE p q) (liftE {e} {e'} f c) ≡ liftE {e''} {e'''} (subE q ∘ f) (subE p c)
sub-monE {e'' = err} reflE q f c = refl
sub-monE {e'' = ok} reflE q f c = refl
sub-monE {e'' = errok} {err} p q f c = refl
sub-monE {e'' = errok} {ok} reflE reflE f c = refl
sub-monE {e'' = errok} {ok} err⊑Eerrok reflE f c = refl
sub-monE {e'' = errok} {ok} ok⊑Eerrok reflE f c = refl
sub-monE {e'' = errok} {errok} reflE reflE f c = refl
sub-monE {e'' = errok} {errok} reflE err⊑Eerrok f (just x) = refl
sub-monE {e'' = errok} {errok} reflE err⊑Eerrok f nothing = refl
sub-monE {e'' = errok} {errok} reflE ok⊑Eerrok f (just x) = refl
sub-monE {e'' = errok} {errok} reflE ok⊑Eerrok f nothing = refl
sub-monE {e'' = errok} {errok} err⊑Eerrok q f c = refl
sub-monE {e'' = errok} {errok} ok⊑Eerrok reflE f c = refl
sub-monE {e'' = errok} {errok} ok⊑Eerrok err⊑Eerrok f c = refl
sub-monE {e'' = errok} {errok} ok⊑Eerrok ok⊑Eerrok f c = refl

sub-transE : {e e' e'' : E} {X : Set} →
             (p : e ⊑E e') → (q : e' ⊑E e'') → (c : TE e X) → 
             subE q (subE p c) ≡ subE (transE p q) c
sub-transE reflE q c = refl
sub-transE err⊑Eerrok reflE c = refl
sub-transE ok⊑Eerrok reflE c = refl

mlaw1E : {e : E} → {X Y : Set} → (f : X → TE e Y) → (x : X) →
         liftE {ok} {e} f (ηE x) ≡ f x
mlaw1E f x = refl

sub-eqE : {e e' : E} {X : Set} → e ≡ e' → TE e X → TE e' X
sub-eqE {e} {.e} refl = subE {e} reflE

mlaw2E :  {e : E} → {X : Set} → (c : TE e X) →
          sub-eqE {e} ruE c ≡ liftE {e} {ok} ηE c
mlaw2E {err} c = refl
mlaw2E {ok} c = refl
mlaw2E {errok} (just x) = refl
mlaw2E {errok} nothing = refl


-- liftE {e} {e'} f c : TE (e ·E e') Y
{-
mlaw3E : {e e' e'' : E} → {X Y Z : Set} → (f : X → TE e' Y) → (g : Y → TE e'' Z) → (c : TE e X) → 
         assE (liftE {{!!}} g (liftE {e} {e'} f c)) ≡ {!!} -- liftE (liftE {e} g ∘ f) c
mlaw3E f g c = {!!}
-}

ExcEffGM : GradedMonad
ExcEffGM = record { OM = ExcEffOM
                  ; T = TE
                  ; η = ηE
                  ; lift = λ {e} {e'} → liftE {e} {e'}
                  ; sub = subE
                  ; sub-mon = sub-monE
                  ; sub-eq = sub-eqE
                  ; sub-refl = λ {e} → sub-reflE {e}
                  ; sub-trans = sub-transE
                  ; mlaw1 = λ {e} → mlaw1E {e}
                  ; mlaw2 = λ {e} → mlaw2E {e}
                  ; mlaw3 = {!!}
                  }
