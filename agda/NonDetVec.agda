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


--ru+ : {n : ℕ} → n + 0 ≡ n
--ru+ {zero} = refl
--ru+ {suc n} = cong suc (ru+ {n}) 
ru+ : {n : ℕ} → n ≡ n + 0
ru+ {zero} = refl
ru+ {suc n} = cong suc (ru+ {n}) 

lu* : {n : ℕ} → 1 * n ≡ n
lu* {zero} = refl
lu* {suc n} = cong suc (lu* {n})

ru* : {n : ℕ} → n ≡ n * 1 
ru* {zero} = refl
ru* {suc n} = cong suc (ru* {n})

ass+ : {m n o : ℕ} → (m + n) + o ≡ m + (n + o)
ass+ {zero} = refl
ass+ {suc m} = cong suc (ass+ {m})

+ass : {m n o : ℕ} → m + (n + o) ≡ (m + n) + o
--+ass {m} {n} {o} = sym (ass+ {m} {n} {o})
+ass {zero} = refl
+ass {suc m} = cong suc (+ass {m})

dist+ : {m n o : ℕ} → (m + n) * o ≡ m * o + n * o
dist+ {zero}  {_} {_} = refl
dist+ {suc m} {n} {o} = trans (cong (_+_ o) (dist+ {m} {n} {o})) 
                              (sym (ass+ {o} {m * o} {n * o}))

ass* : {m n o : ℕ} → (m * n) * o ≡ m * (n * o) -- ⊑
ass* {zero} = refl
ass* {suc m} {n} {o} =
                begin
                  (n + m * n) * o
                ≡⟨ dist+ {n} {m * n} {o}  ⟩
                  n * o + (m * n) * o
                ≡⟨ cong (λ x → n * o + x) (ass* {m} {n} {o}) ⟩
                  n * o + m * (n * o)
                ∎
zl* : {m : ℕ} → m * 0 ≡ 0
zl* {zero} = refl
zl* {suc m} = zl* {m}
zr* : {m : ℕ} → 0 ≡ m * 0
zr* {zero} = refl
zr* {suc m} = zr* {m}


ℕ* : OrderedMonoid
ℕ* = record { M = ℕ
             ; _⊑_ = _≡_
             ; reflM = refl
             ; transM = trans
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
--subV {X = X} p = subst (Vec X) p
--subV refl xs = xs
subV  = subeq {ℕ} {λ n X → Vec X n}

{-
subV∷ : {m n : ℕ} → {X : Set} → {x : X} → {xs : Vec X m}    
    (p : m ≡ n) → subV (cong suc p) (x ∷ xs) ≡ x ∷ subV p xs 
subV∷ refl  = refl
-}

subV∷ : {m n : ℕ} → {X : Set} → {x : X} → {xs : Vec X m} → {ys : Vec X n} →    
    (p : m ≡ n) → subV p xs ≡ ys → subV (cong suc p) (x ∷ xs) ≡ x ∷ ys 
subV∷ refl refl = refl


sub-mon : {e e' e'' e''' : M} {X Y : Set} (p : e ⊑ e'') (q : e' ⊑ e''')
      (f : X → Vec Y e') (c : Vec X e) →
      subV (mon p q) (liftV f c) ≡
      liftV ((subV q) ∘ f) (subV p c)
sub-mon refl refl f c = refl 

ru++ : {n : ℕ} → {X : Set} → (xs : Vec X n) → subV lu (xs ++ []) ≡ xs
ru++ []       = refl
ru++ (x ∷ xs) = subV∷ lu (ru++ xs)
{-
  begin 
    subV (cong suc ru+) (x ∷ xs ++ []) 
  ≡⟨ subV∷ ru+ ⟩ 
    x ∷ subV ru+ (xs ++ [])
  ≡⟨ cong (_∷_ x) (ru++ xs) ⟩ 
    x ∷ xs 
  ∎
-}

sub-refl : {e : M} {X : Set} (c : Vec X e) → subV reflM c ≡ c
sub-refl _ = refl

sub-trans : {e e' e'' : M} {X : Set} (p : e ⊑ e') (q : e' ⊑ e'')
      (c : Vec X e) →
      subV q (subV p c) ≡ subV (transM p q) c
sub-trans refl refl c = refl
mlaw1V : {n : ℕ} → {X Y : Set} → (f : X → Vec Y n) → (x : X) →
            subV lu (liftV f (ηV x)) ≡ f x
mlaw1V f x = ru++ (f x)


mlaw2V : {n : ℕ} → {X : Set} → (xs : Vec X n) →
            subV ru xs ≡ liftV ηV xs
mlaw2V []       = refl
mlaw2V (x ∷ xs) = subV∷ {x = x} {xs = xs} ru (mlaw2V xs) 

lem1 : {m n : M} → m + suc n ≡ suc m + n
lem1 {zero} = refl
lem1 {suc m} {n} = cong suc (lem1 {m})

comm+ : {m n : M} → m + n ≡ n + m
comm+ {zero} = ru+
comm+ {suc m} {zero} = cong suc (comm+ {m})
comm+ {suc m} {suc n} = cong suc (
  begin
    m + suc n
  ≡⟨ lem1 {m} {n} ⟩
    suc m + n
  ≡⟨ comm+ {suc m} ⟩
    n + suc m 
  ∎)

-- FIXME :-)
comm* : {m n : M} → m * n ≡ n * m
comm* {zero} {n} = zr* {n}
comm* {suc m} {zero} = comm* {m}
comm* {suc m} {suc n} = cong suc (
  begin
    n + m * suc n
  ≡⟨ cong (_+_ n) (comm* {m}) ⟩
    n + suc n * m
  ≡⟨ cong (_+_ n) (comm+ {m}) ⟩
    n + (n * m + m)
  ≡⟨ cong (_+_ n) (cong (λ x → x + m) (comm* {n})) ⟩
    n + (m * n + m)
  ≡⟨ sym (ass+ {n}) ⟩
    (n + m * n) + m
  ≡⟨ comm+ {n + m * n} ⟩
    m + suc m * n
  ≡⟨ cong (_+_ m) (comm* {suc m} {n}) ⟩
    m + n * suc m
  ∎)



lemmm :  {e' : M} → 
         ass* {suc zero} {suc e'} {zero}
         ≡ ass* {suc zero} {e'} {zero}
lemmm {e'} = 
  begin
    ass* {suc zero} {suc e'} {zero}
  ≡⟨ cong {!!} (comm* {suc e'} {zero}) ⟩
    {!!}
  ≡⟨ {!!} ⟩
    ass* {suc zero} {e'} {zero}
  ∎

lemma' : {e' e'' : M} {X Y Z : Set}
        (g : Y → Vec Z e'')
        (ys : Vec Y e')
         →
        subV (ass* {suc zero} {e'} {e''}) (liftV g (ys ++ []))
        ≡ liftV g ys ++ []
lemma' g [] = refl
lemma' {suc e'} g (y ∷ ys) with g y
lemma' {suc e'} {zero} {X} {Y} {Z} g (y ∷ ys) | [] =
  begin
    subV (ass* {suc zero} {suc e'} {zero} ) (liftV g (ys ++ []))
  ≡⟨ cong (λ p → subV p (liftV g (ys ++ []))) (lemmm {e'}) ⟩
    subV (ass* {suc zero} {e'} {zero} ) (liftV g (ys ++ []))
  ≡⟨ lemma' {e'} {zero} {X} {Y} {Z} g ys ⟩
    liftV g ys ++ []
  ∎
lemma' {suc e'} g (y ∷ ys) | z ∷ zs = {!!}


lemma-sub++ : {e e' E E' : M} 
             {p : e ⊑ E} {q : e' ⊑ E'} {r : (e + e') ⊑ (E + E')}
             {X : Set}
             (xs : Vec X e) (xs' : Vec X e') →
             subV p xs ++ subV q xs' ≡ subV r (xs ++ xs')
lemma-sub++ {p = refl} {q = refl} {r = refl} [] xs' = refl
lemma-sub++ {suc e} {e'} {E = suc .e} {E' = .e'} {p = refl} {q = refl} {r = refl} (x ∷ xs) xs' = 
  begin
    subV refl (x ∷ xs) ++ subV refl xs'
  ≡⟨ refl ⟩
    x ∷ (subV refl xs) ++ subV refl xs'
  ≡⟨ cong (_∷_ x) (lemma-sub++ {p = refl} {q = refl} {r = cong (_+_ e) refl} xs xs') ⟩
    x ∷ (subV (cong (_+_ e) refl) (xs ++ xs'))
  ≡⟨ sym (subV∷ (cong (_+_ e) refl) refl) ⟩
    subV (cong suc (cong (_+_ e) refl)) (x ∷ xs ++ xs')
  ≡⟨ refl ⟩
    subV refl (x ∷ xs ++ xs')
  ∎

ass+* : {m n o : ℕ} → n * o + m * n * o ≡ n * o + m * (n * o) --suc m * (n * o)
ass+* {m} {n} {o} = cong (_+_ (n * o)) (ass* {m} {n} {o})

lemma2 : {e e' e'' : M} {X Y Z : Set}
        (g : Y → Vec Z e'')
        (f : X → Vec Y e') (x : X)
        (ys' : Vec Y (e * e')) →
        (liftV g (f x)) ++ subV (ass* {e} {e'} {e''}) (liftV g ys')
        ≡
        subV (ass* {suc e} {e'} {e''}) (liftV g ((f x) ++ ys'))
lemma2 {e} {e'} {e''} g f x ys' = 
  begin
    (liftV g (f x)) ++ subV (ass* {e} {e'} {e''}) (liftV g ys')
  ≡⟨ lemma-sub++ {e' * e''} {e * e' * e''} {e' * e''} {e * (e' * e'')}
                 {refl} {ass* {e} {e'} {e''}} {ass+* {e} {e'} {e''}}
                 (liftV g (f x)) (liftV g ys') ⟩ 
    subV (ass+* {e} {e'} {e''}) ((liftV g (f x)) ++ (liftV g ys'))
  ≡⟨ {!!} ⟩
    subV (ass* {suc e} {e'} {e''}) (liftV g ((f x) ++ ys'))
  ∎

lemma++ : {e e' e'' : M} {X : Set}
          (xs : Vec X e) (xs' : Vec X e') (xs'' : Vec X e'') →
          subV (ass+ {e} {e'} {e''}) ((xs ++ xs') ++ xs'')
          ≡ xs ++ (xs' ++ xs'')
lemma++ [] xs' xs'' = refl
lemma++ {suc e} {e'} {e''} (x ∷ xs) xs' xs'' = subV∷ (ass+ {e} {e'} {e''}) (lemma++ xs xs' xs'')

lemma++2 : {e e' e'' : M} {X : Set}
          (xs : Vec X e) (xs' : Vec X e') (xs'' : Vec X e'') →
          subV (+ass {e} {e'} {e''}) (xs ++ (xs' ++ xs''))
          ≡ (xs ++ xs') ++ xs''
lemma++2 [] xs' xs'' = refl
lemma++2 {suc e} {e'} {e''} (x ∷ xs) xs' xs'' = subV∷ (+ass {e} {e'} {e''}) (lemma++2 xs xs' xs'')

-- dist+ {suc e} {e'} {e''} :
--         e'' + (e + e') * e'' ≡ e'' + e * e'' + e' * e''
-- +ass {e''} {e * e''} {e' * e''}:
--         e'' + (e * e'' + e' * e'') ≡ e'' + e * e'' + e' * e''

lemma-that : {e e' e'' : M} {X Y : Set}
             (f : X → Vec Y e'')
             (ys : Vec Y e'')
             (xs : Vec X e)
             (xs' : Vec X e') →
             subV (dist+ {suc e} {e'} {e''})
                  (ys ++ liftV f (xs ++ xs'))
             ≡ subV (+ass {e''} {e * e''} {e' * e''})
                    (ys ++ subV (dist+ {e} {e'} {e''}) (liftV f (xs ++ xs')))
lemma-that f [] xs xs' = {!!}
lemma-that f (y ∷ ys) xs xs' = {!!}


lemma-other : {e e' e'' : M} {X Y : Set}
              (f : X → Vec Y e'')
              (xs : Vec X e)
              (xs' : Vec X e') →
              subV (dist+ {e} {e'} {e''}) (liftV f (xs ++ xs'))
              ≡ liftV f xs ++ liftV f xs'
lemma-other f [] xs' = refl
lemma-other {suc e} {e'} {e''} f (x ∷ xs) xs' =
  begin
    subV (dist+ {suc e} {e'} {e''}) (liftV f (x ∷ xs ++ xs'))
  ≡⟨ refl ⟩
    subV (dist+ {suc e} {e'} {e''}) (f x ++ (liftV f (xs ++ xs')))
  ≡⟨ lemma-that f (f x) xs xs' ⟩
    subV (+ass {e''} {e * e''} {e' * e''})
         (f x ++ subV (dist+ {e} {e'} {e''}) (liftV f (xs ++ xs')))
  ≡⟨ cong (λ ys → subV (+ass {e''} {e * e''} {e' * e''}) (f x ++ ys))
          (lemma-other {e} {e'} {e''} f xs xs') ⟩ 
    subV (+ass {e''} {e * e''} {e' * e''}) (f x ++ (liftV f xs ++ liftV f xs'))
  ≡⟨ lemma++2 (f x) (liftV f xs) (liftV f xs') ⟩
    (f x ++ liftV f xs) ++ liftV f xs'
  ≡⟨ refl ⟩
    liftV f (x ∷ xs) ++ liftV f xs'
  ∎

lemma : {e e' e'' : M} {X Y Z : Set}
        (g : Y → Vec Z e'')
        (f : X → Vec Y e') (x : X)
        (ys' : Vec Y (e * e')) →
        subV (ass* {suc e} {e'} {e''}) (liftV g ((f x) ++ ys'))
        ≡ liftV g (f x) ++ subV (ass* {e} {e'} {e''}) (liftV g ys')
lemma {e} {e'} {e''} g f x ys' with f x
... | ys = {!!}


mlaw3V : {e e' e'' : M} {X Y Z : Set} (f : X → Vec Y e')
      (g : Y → Vec Z e'') (c : Vec X e) →
      subV (ass* {e} {e'} {e''}) (liftV g (liftV f c))
      ≡ liftV (λ x → liftV g (f x)) c
mlaw3V f g [] = refl
mlaw3V {suc e} {e'} {e''} f g (x ∷ xs) =
  begin
    subV (ass* {suc e} {e'} {e''}) (liftV g (liftV f (x ∷ xs)))
  ≡⟨ refl ⟩
    subV (ass* {suc e} {e'} {e''}) (liftV g (f x ++ liftV f xs))
  ≡⟨ lemma {e} {e'} {e''} g f x (liftV f xs) ⟩
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
