module NonDetVec where

open import Function
--open import Data.List
--open import Relation.Nullary


--open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality hiding ([_]; inspect)

--open import Finiteness
open import OrderedMonoid
open import GradedMonad

open import Data.Nat
open import Data.Vec

open ≡-Reasoning


lu* : {n : ℕ} → 1 * n ≡ n
lu* {zero} = refl
lu* {suc n} = cong suc (lu* {n})

ru* : {n : ℕ} → n ≡ n * 1 
ru* {zero} = refl
ru* {suc n} = cong suc (ru* {n})

+ass : {m n o : ℕ} → m + (n + o) ≡ (m + n) + o
+ass {zero} = refl
+ass {suc m} = cong suc (+ass {m})

dist+ : {m n o : ℕ} → (m + n) * o ≡ m * o + n * o
dist+ {zero}  {_} {_} = refl
dist+ {suc m} {n} {o} = trans (cong (_+_ o) (dist+ {m} {n} {o})) 
                              (+ass {o} {m * o} {n * o})

ass* : {m n o : ℕ} → (m * n) * o ≡ m * (n * o)
ass* {zero} = refl
ass* {suc m} {n} {o} = trans (dist+ {n} {m * n} {o})
                             (cong (_+_ (n * o)) (ass* {m} {n} {o}))


ℕ* : OrderedMonoid
ℕ* = record { E = ℕ
            ; _⊑_ = _≡_
            ; ⊑-refl = refl
            ; ⊑-trans = trans
            ; i = 1
            ; _·_ = _*_
            ; mon = cong₂ _*_
            ; lu = lu* 
            ; ru =  ru* 
            ; ass = λ {m n o} → ass* {m} {n} {o}
            }

open OrderedMonoid.OrderedMonoid ℕ*
 
ηV : {X : Set} → X → Vec X 1
ηV x = x ∷ [] 


liftV : {m n : ℕ} {X Y : Set} →
        (X → Vec Y n) → Vec X m → Vec Y (m * n)
liftV f [] =  []
liftV f (x ∷ xs) =  f x ++ liftV f xs


subV : {n n' : ℕ} {X : Set} → n ⊑ n' → Vec X n → Vec X n'
subV  = subeq {ℕ} {λ n X → Vec X n}


subV∷ : {m n : ℕ} {X : Set} {x : X} {xs : Vec X m} {ys : Vec X n} →    
        (p : m ≡ n) → subV p xs ≡ ys → subV (cong suc p) (x ∷ xs) ≡ x ∷ ys 
subV∷ refl refl = refl


sub-mon : {e e' e'' e''' : E} {X Y : Set} (p : e ⊑ e'') (q : e' ⊑ e''')
          (f : X → Vec Y e') (c : Vec X e) →
          subV (mon p q) (liftV f c) ≡
          liftV ((subV q) ∘ f) (subV p c)
sub-mon refl refl f c = refl 


ru++ : {n : ℕ} → {X : Set} → (xs : Vec X n) → subV lu (xs ++ []) ≡ xs
ru++ []       = refl
ru++ (x ∷ xs) = subV∷ lu (ru++ xs)


sub-refl : {e : E} {X : Set} (c : Vec X e) → subV ⊑-refl c ≡ c
sub-refl _ = refl


sub-trans : {e e' e'' : E} {X : Set} (p : e ⊑ e') (q : e' ⊑ e'')
      (c : Vec X e) →
      subV q (subV p c) ≡ subV (⊑-trans p q) c
sub-trans refl refl c = refl


mlaw1V : {n : ℕ} {X Y : Set} → (f : X → Vec Y n) → (x : X) →
         subV lu (liftV f (ηV x)) ≡ f x
mlaw1V f x = ru++ (f x)


mlaw2V : {n : ℕ} {X : Set} → (xs : Vec X n) →
         subV ru xs ≡ liftV ηV xs
mlaw2V []       = refl
mlaw2V (x ∷ xs) = subV∷ {x = x} {xs = xs} ru (mlaw2V xs) 


lemma++ : {e e' e'' : E} {X : Set}
          (xs : Vec X e) (xs' : Vec X e') (xs'' : Vec X e'') →
          subV (+ass {e} {e'} {e''}) (xs ++ (xs' ++ xs''))
          ≡ (xs ++ xs') ++ xs''
lemma++ [] xs' xs'' = refl
lemma++ {suc e} {e'} {e''} (x ∷ xs) xs' xs'' = subV∷ (+ass {e} {e'} {e''}) (lemma++ xs xs' xs'')


subV-lemma : {e e' : E} {X Y : Set} →
             (g : E → E) → (f : {e : E} → Vec X e → Vec Y (g e)) →
             (p : e ≡ e') → (xs : Vec X e) →
             subV (cong g p) (f xs) ≡ f (subV p xs)
subV-lemma g f refl xs =  refl


lemma-dist : {e e' e'' : E} {X Y : Set}
             (xs : Vec X e)
             (xs' : Vec X e')
             (f : X → Vec Y e'') →
             subV (dist+ {e} {e'} {e''}) (liftV f (xs ++ xs'))
             ≡ liftV f xs ++ liftV f xs'
lemma-dist [] xs' f = refl
lemma-dist {suc e} {e'} {e''} (x ∷ xs) xs' f =
  begin
    subV (dist+ {suc e} {e'} {e''}) (liftV f (x ∷ xs ++ xs'))
  ≡⟨ refl ⟩
    subV (dist+ {suc e} {e'} {e''}) (f x ++ (liftV f (xs ++ xs')))
  ≡⟨ sym (sub-trans (cong (_+_ e'') (dist+ {e} {e'} {e''})) (+ass {e''} {e * e''} {e' * e''}) _) ⟩
    subV (+ass {e''} {e * e''} {e' * e''})
         (subV (cong (_+_ e'') (dist+ {e} {e'} {e''})) (f x ++ liftV f (xs ++ xs')))
  ≡⟨ cong (subV (+ass {e''} {e * e''} {e' * e''}))
          (subV-lemma (_+_ e'') (_++_ (f x)) (dist+ {e} {e'} {e''}) (liftV f (xs ++ xs'))) ⟩
    subV (+ass {e''} {e * e''} {e' * e''})
         (f x ++ subV (dist+ {e} {e'} {e''}) (liftV f (xs ++ xs')))
  ≡⟨ cong (λ ys → subV (+ass {e''} {e * e''} {e' * e''}) (f x ++ ys))
          (lemma-dist {e} {e'} {e''} xs xs' f) ⟩ 
    subV (+ass {e''} {e * e''} {e' * e''}) (f x ++ (liftV f xs ++ liftV f xs'))
  ≡⟨ lemma++ (f x) (liftV f xs) (liftV f xs') ⟩
    (f x ++ liftV f xs) ++ liftV f xs'
  ≡⟨ refl ⟩
    liftV f (x ∷ xs) ++ liftV f xs'
  ∎

mlaw3V : {e e' e'' : E} {X Y Z : Set} (f : X → Vec Y e')
         (g : Y → Vec Z e'') (c : Vec X e) →
         subV (ass* {e} {e'} {e''}) (liftV g (liftV f c))
         ≡ liftV (λ x → liftV g (f x)) c
mlaw3V f g [] = refl
mlaw3V {suc e} {e'} {e''} f g (x ∷ xs) =
  begin
    subV (ass* {suc e} {e'} {e''}) (liftV g (liftV f (x ∷ xs)))
  ≡⟨ refl ⟩
    subV (ass* {suc e} {e'} {e''}) (liftV g (f x ++ liftV f xs))
  ≡⟨ sym (sub-trans (dist+ {e'} {e * e'} {e''}) (cong (_+_ (e' * e'')) (ass* {e} {e'} {e''})) _)  ⟩
    subV (cong (_+_ (e' * e'')) (ass* {e} {e'} {e''}))
       (subV (dist+ {e'} {e * e'} {e''}) (liftV g (f x ++ liftV f xs)))
  ≡⟨ cong (subV (cong (_+_ (e' * e'')) (ass* {e} {e'} {e''}))) (lemma-dist (f x) (liftV f xs) g) ⟩ 
    subV (cong (_+_ (e' * e'')) (ass* {e} {e'} {e''}))
        (liftV g (f x) ++ liftV g (liftV f xs))
  ≡⟨ subV-lemma (_+_ (e' * e'')) (_++_ (liftV g (f x))) (ass* {e} {e'} {e''}) _  ⟩ 
     (liftV g (f x) ++ subV (ass* {e} {e'} {e''}) (liftV g (liftV f xs)))
  ≡⟨ cong (_++_ (liftV g (f x))) (mlaw3V f g xs) ⟩
    liftV g (f x) ++ liftV (λ x → liftV g (f x)) xs
  ≡⟨ refl ⟩
    liftV (λ x → liftV g (f x)) (x ∷ xs)
  ∎

NDV : GradedMonad
NDV = record { OM = ℕ*
             ; T = λ e X → Vec X e
             ; η = ηV
             ; lift = liftV 
             ; sub = subV 
             ; sub-mon = sub-mon
             ; sub-refl = sub-refl
             ; sub-trans = sub-trans
             ; mlaw1 = mlaw1V
             ; mlaw2 = mlaw2V
             ; mlaw3 = mlaw3V
             }
