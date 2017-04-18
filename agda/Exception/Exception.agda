module Exception where

open import Data.Maybe
open import Data.Maybe.Base
open import Data.Unit
open import Function
open import Relation.Binary.Core using (_≡_ ; refl)
open import Relation.Nullary

open import Relation.Binary.PropositionalEquality

open import Grading


data Exc : Set where
  err : Exc
  ok : Exc
  errok : Exc

private

  data _⊑_ : Exc → Exc → Set where
    ⊑-refl : {e : Exc} → e ⊑ e
    err⊑errok : err ⊑ errok
    ok⊑errok : ok ⊑ errok


  ⊑-trans : {e e' e'' : Exc} → e ⊑ e' → e' ⊑ e'' → e ⊑ e''
  ⊑-trans ⊑-refl q = q
  ⊑-trans err⊑errok ⊑-refl = err⊑errok
  ⊑-trans ok⊑errok ⊑-refl = ok⊑errok


  _·_ : Exc → Exc → Exc
  ok · e = e
  err · e = err
  errok · err = err
  errok · ok = errok
  errok · errok = errok


  ru : {e : Exc} →  e ≡ e · ok 
  ru {err} = refl
  ru {ok} = refl
  ru {errok} = refl


  ass : {e e' e'' : Exc} → (e · e') · e'' ≡ e · (e' · e'')
  ass {err} = refl
  ass {ok} = refl
  ass {errok} {err} = refl
  ass {errok} {ok} = refl
  ass {errok} {errok} {err} = refl
  ass {errok} {errok} {ok} = refl
  ass {errok} {errok} {errok} = refl


  mon : {e e' e'' e''' : Exc} → e ⊑ e'' → e' ⊑ e''' → e · e' ⊑ e'' · e'''
  mon {e'' = err} ⊑-refl q = ⊑-refl
  mon {e'' = ok} ⊑-refl q = q
  mon {e'' = errok} {err} ⊑-refl ⊑-refl = ⊑-refl
  mon {e'' = errok} {err} err⊑errok ⊑-refl = ⊑-refl
  mon {e'' = errok} {err} ok⊑errok ⊑-refl = ⊑-refl
  mon {e'' = errok} {ok} ⊑-refl ⊑-refl = ⊑-refl
  mon {e'' = errok} {ok} err⊑errok ⊑-refl = err⊑errok
  mon {e'' = errok} {ok} ok⊑errok ⊑-refl = ok⊑errok
  mon {e'' = errok} {errok} ⊑-refl ⊑-refl = ⊑-refl
  mon {e'' = errok} {errok} ⊑-refl err⊑errok = err⊑errok
  mon {e'' = errok} {errok} ⊑-refl ok⊑errok = ⊑-refl
  mon {e'' = errok} {errok} err⊑errok q = err⊑errok
  mon {e'' = errok} {errok} ok⊑errok ⊑-refl = ⊑-refl
  mon {e'' = errok} {errok} ok⊑errok err⊑errok = err⊑errok
  mon {e'' = errok} {errok} ok⊑errok ok⊑errok = ok⊑errok


ExcEffOM : OrderedMonoid
ExcEffOM = record { E = Exc
                  ; _·_ = _·_
                  ; i = ok
                  
                  ; lu = refl
                  ; ru = ru 
                  ; ass = λ {m} {n} {o} → ass {m} {n} {o}
                  
                  ; _⊑_ = _⊑_ 
                  ; ⊑-refl = ⊑-refl
                  ; ⊑-trans = ⊑-trans
                  
                  ; mon = mon
                  }

private

  T : Exc → Set → Set
  T err X = ⊤
  T ok X = X
  T errok X = Maybe X

  η : {X : Set} → X → T ok X
  η x = x

  bind : {e e' : Exc} {X Y : Set} →
         (X → T e' Y) → T e X → T (e · e') Y
  bind {err} f x = tt
  bind {ok} f x = f x
  bind {errok} {err} f x = tt
--  bind {errok} {ok} f x = map f x
  bind {errok} {ok} f (just x) = just (f x)
  bind {errok} {ok} f nothing = nothing
  bind {errok} {errok} f (just x) = f x
  bind {errok} {errok} f nothing = nothing


  sub : {e e' : Exc} {X : Set} → e ⊑ e' → T e X → T e' X
  sub ⊑-refl c = c
  sub err⊑errok c = nothing
  sub ok⊑errok x = just x


  sub-refl : {e : Exc} {X : Set} → (c : T e X) → sub {e} ⊑-refl c ≡ c
  sub-refl _ = refl


  sub-mon : {e e' e'' e''' : Exc} {X Y : Set} →
            (p : e ⊑ e'') → (q : e' ⊑ e''') →
            (f : X → T e' Y) → (c : T e X) → 
            sub (mon p q) (bind {e} {e'} f c) ≡ bind {e''} {e'''} (sub q ∘ f) (sub p c)
  sub-mon {e'' = err} ⊑-refl q f c = refl
  sub-mon {e'' = ok} ⊑-refl q f c = refl
  sub-mon {e'' = errok} {err} p q f c = refl
  sub-mon {e'' = errok} {ok} ⊑-refl ⊑-refl f c = refl
  sub-mon {e'' = errok} {ok} err⊑errok ⊑-refl f c = refl
  sub-mon {e'' = errok} {ok} ok⊑errok ⊑-refl f c = refl
  sub-mon {e'' = errok} {errok} ⊑-refl ⊑-refl f c = refl
  sub-mon {e'' = errok} {errok} ⊑-refl err⊑errok f (just x) = refl
  sub-mon {e'' = errok} {errok} ⊑-refl err⊑errok f nothing = refl
  sub-mon {e'' = errok} {errok} ⊑-refl ok⊑errok f (just x) = refl
  sub-mon {e'' = errok} {errok} ⊑-refl ok⊑errok f nothing = refl
  sub-mon {e'' = errok} {errok} err⊑errok q f c = refl
  sub-mon {e'' = errok} {errok} ok⊑errok ⊑-refl f c = refl
  sub-mon {e'' = errok} {errok} ok⊑errok err⊑errok f c = refl
  sub-mon {e'' = errok} {errok} ok⊑errok ok⊑errok f c = refl


  sub-trans : {e e' e'' : Exc} {X : Set} →
              (p : e ⊑ e') → (q : e' ⊑ e'') → (c : T e X) → 
              sub q (sub p c) ≡ sub (⊑-trans p q) c
  sub-trans ⊑-refl q c = refl
  sub-trans err⊑errok ⊑-refl c = refl
  sub-trans ok⊑errok ⊑-refl c = refl


  mlaw1 : {e : Exc} → {X Y : Set} → (f : X → T e Y) → (x : X) →
          bind {ok} {e} f (η x) ≡ f x
  mlaw1 f x = refl


  sub-eq : {e e' : Exc} {X : Set} → e ≡ e' → T e X → T e' X
  sub-eq = subeq {Exc} {T}


  mlaw2 :  {e : Exc} → {X : Set} → (c : T e X) →
           sub-eq {e} ru c ≡ bind {e} η c
  mlaw2 {err} c = refl
  mlaw2 {ok} c = refl
  mlaw2 {errok} (just x) = refl
  mlaw2 {errok} nothing = refl


  mlaw3 : {e e' e'' : Exc} → {X Y Z : Set} →
          (f : X → T e' Y) → (g : Y → T e'' Z) → (c : T e X) → 
          sub-eq {(e · e') · e''} {e · (e' · e'')}
                 (ass {e} {e'} {e''})
                 (bind {e · e'} {e''} g (bind {e} {e'} f c))
          ≡ bind {e} {e' · e''} (bind {e'} {e''} g ∘ f) c
  mlaw3 {err} f g c = refl
  mlaw3 {ok} f g c = refl
  mlaw3 {errok} {err} f g c = refl
  mlaw3 {errok} {ok} {err} f g c = refl
  mlaw3 {errok} {ok} {ok} f g (just x) = refl
  mlaw3 {errok} {ok} {ok} f g nothing = refl
  mlaw3 {errok} {ok} {errok} f g (just x) = refl
  mlaw3 {errok} {ok} {errok} f g nothing = refl
  mlaw3 {errok} {errok} {err} f g c = refl
  mlaw3 {errok} {errok} {ok} f g (just x) = refl
  mlaw3 {errok} {errok} {ok} f g nothing = refl
  mlaw3 {errok} {errok} {errok} f g (just x) = refl
  mlaw3 {errok} {errok} {errok} f g nothing = refl


ExcEffGM : GradedMonad
ExcEffGM = record { OM = ExcEffOM
                  ; T = T
                  ; η = η
                  ; bind = λ {e} {e'} → bind {e} {e'}
                  ; sub = sub
                  ; sub-mon = sub-mon
                  ; sub-refl = λ {e} → sub-refl {e}
                  ; sub-trans = sub-trans
                  ; mlaw1 = λ {e} → mlaw1 {e}
                  ; mlaw2 = λ {e} → mlaw2 {e}
                  ; mlaw3 = λ {e} {e'} {e''} → mlaw3 {e} {e'} {e''}
                  }

-------------------------------------------------------------------------

infix 110 _·_
infix 100 _⊔_ _⊓_

_⊔_ : Exc → Exc → Exc
err ⊔ err = err
ok ⊔ ok = ok
_ ⊔ _ = errok


⊔-sym : (e e' : Exc) → e ⊔ e' ≡ e' ⊔ e
⊔-sym err err = refl
⊔-sym err ok = refl
⊔-sym err errok = refl
⊔-sym ok err = refl
⊔-sym ok ok = refl
⊔-sym ok errok = refl
⊔-sym errok err = refl
⊔-sym errok ok = refl
⊔-sym errok errok = refl


lub : (e e' : Exc) → e ⊑ (e ⊔ e')
lub err err = ⊑-refl
lub err ok = err⊑errok
lub err errok = err⊑errok
lub ok err = ok⊑errok
lub ok ok = ⊑-refl
lub ok errok = ok⊑errok
lub errok err = ⊑-refl
lub errok ok = ⊑-refl
lub errok errok = ⊑-refl


lub-sym : (e e' : Exc) → e ⊑ (e' ⊔ e)
lub-sym e e' rewrite ⊔-sym e' e = lub e e'

⊔-itself : (e : Exc) → e ⊔ e ≡ e
⊔-itself err = refl
⊔-itself ok = refl
⊔-itself errok = refl

---------------------------

infix 120 _⊹_
_⊹_ : Exc → Exc → Exc
err ⊹ e' = e'
ok ⊹ _ = ok
errok ⊹ ok = ok
errok ⊹ _ = errok

--------------------------------
-- deciders

_≡E?_ : (e e' : Exc) → Dec (e ≡ e')
err ≡E? err = yes refl
err ≡E? ok = no (λ ())
err ≡E? errok = no (λ ())
ok ≡E? err = no (λ ())
ok ≡E? ok = yes refl
ok ≡E? errok = no (λ ())
errok ≡E? err = no (λ ())
errok ≡E? ok = no (λ ())
errok ≡E? errok = yes refl

_⊑?_ : (e e' : Exc) → Dec (e ⊑ e')
err ⊑? err = yes ⊑-refl
err ⊑? ok = no (λ ())
err ⊑? errok = yes err⊑errok
ok ⊑? err = no (λ ())
ok ⊑? ok = yes ⊑-refl
ok ⊑? errok = yes ok⊑errok
errok ⊑? err = no (λ ())
errok ⊑? ok = no (λ ())
errok ⊑? errok = yes ⊑-refl

-------------------------------------

_⊓_ : Exc → Exc → Maybe Exc
err ⊓ err = just err
err ⊓ ok = nothing
err ⊓ errok = just err
ok ⊓ err = nothing
ok ⊓ ok = just ok
ok ⊓ errok = just ok
errok ⊓ e' = just e'

⊓-sym : (e e' : Exc) → e ⊓ e' ≡ e' ⊓ e
⊓-sym err err = refl
⊓-sym err ok = refl
⊓-sym err errok = refl
⊓-sym ok err = refl
⊓-sym ok ok = refl
⊓-sym ok errok = refl
⊓-sym errok err = refl
⊓-sym errok ok = refl
⊓-sym errok errok = refl

glb : (e e' : Exc) {e'' : Exc} → e ⊓ e' ≡ just e'' → e'' ⊑ e
glb err err refl = ⊑-refl
glb err ok ()
glb err errok refl = ⊑-refl
glb ok err ()
glb ok ok refl = ⊑-refl
glb ok errok refl = ⊑-refl
glb errok err refl = err⊑errok
glb errok ok refl = ok⊑errok
glb errok errok refl = ⊑-refl

