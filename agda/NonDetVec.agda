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

dist+ : {m n o : ℕ} → (m + n) * o ≡ m * o + n * o
dist+ {zero}  {_} {_} = refl
dist+ {suc m} {n} {o} = trans (cong (_+_ o) (dist+ {m} {n} {o})) 
                              (sym (ass+ {o} {m * o} {n * o}))

ass* : {m n o : ℕ} → (m * n) * o ≡ m * (n * o)
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


subV : {n n' : ℕ} {X : Set} → n ≡ n' → Vec X n → Vec X n'
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

eze : {e e'' : M} → e * zero * e'' ≡ e * zero
eze {e} {e''} = 
    begin
      (e * zero) * e''
    ≡⟨ cong (λ n → n * e'') (zl* {e}) ⟩
      0
    ≡⟨ zr* {e} ⟩
      e * zero
    ∎
aza : {e e'' : M} → e * zero ≡ {!!}
aza = {!!}
izi : {e e'' : M} → (e * zero) * e'' ≡ e * (zero * e'')
izi = {!!}
ass2 : {m n o : ℕ} → (m * n) * o ≡ m * (n * o)
ass2 = {!!}
t = trans
-- ass* : {m n o : ℕ} → (m * n) * o ≡ m * (n * o)
lass : {e e'' : M} → ass* {suc e} {zero} {e''} ≡ ass* {e} {zero} {e''}
lass {e} {e''} = {!!}

lemm1 : {e : M} {X : Set}
        (xs : Vec X e) →
        subV ru+ (xs) ≡ xs ++ []
lemm1 [] = refl
lemm1 (x ∷ xs) = subV∷ {xs = xs} ru+ (lemm1 xs)

lemm2 : {e' : M} → (e' + zero) * 0 ≡ e' * 0 + 0
lemm2 {e'} = 
  begin
    (e' + zero) * 0
  ≡⟨ cong (λ e → e * 0) ((sym (ru+ {e'}))) ⟩
    e' * 0
  ≡⟨ ru+ ⟩
    e' * 0 + 0
  ∎

lemm3 : {e' : M} →
        ass* {suc zero} {suc e'} {zero}
        ≡ lemm2 {e'}
lemm3 = {!!}

lemm4 : {e' : M} →  e' * 0 + 0 ≡ 0
lemm4 = {!!}
 
lemma' : {e' e'' : M} {X Y Z : Set}
        (g : Y → Vec Z e'')
        (ys : Vec Y e')
         →
        subV (ass* {suc zero} {e'} {e''}) (liftV g (ys ++ []))
        ≡ liftV g ys ++ []
lemma' g [] = refl
lemma' {suc e'} g (y ∷ ys) with g y
lemma' {suc e'} {zero} {X} {Y} {Z} g (y ∷ ys) | [] = -- lemma' g ys ja lemm1
  begin
    --subeq (trans (trans (cong (_+_ 0) dist+) refl) refl)
    --  (liftV g (ys ++ []))
    subV (ass* {suc zero} {suc e'} {zero} ) (liftV g (ys ++ []))
  ≡⟨ {!!} ⟩
    subV (ass* {suc zero} {e'} {zero} ) (liftV g (ys ++ []))
  ≡⟨ lemma' {e'} {zero} {X} {Y} {Z} g ys ⟩ -- lemma' g ys
    liftV g ys ++ []
  ∎
{-  begin
    --subeq (trans (trans (cong (_+_ 0) dist+) refl) refl)
    --  (liftV g (ys ++ []))
    subV (ass* {suc zero} {suc e'} {zero} ) (liftV g (ys ++ []))
  ≡⟨ cong (λ p → subV p (liftV g (ys ++ []))) (lemm3 {e'}) ⟩
    subV (lemm2 {e'}) (liftV g (ys ++ []))
  ≡⟨ {!!} ⟩
    subV ru+ (liftV g ys)
  ≡⟨ lemm1 (liftV g ys) ⟩
    liftV g ys ++ []
  ∎-}
lemma' {suc e'} g (y ∷ ys) | z ∷ zs = {!!}
        
lemma : {e e' e'' : M} {X Y Z : Set}
        (g : Y → Vec Z e'')
        (f : X → Vec Y e') (x : X)
        (ys' : Vec Y (e * e')) →
        subV (ass* {suc e} {e'} {e''}) (liftV g ((f x) ++ ys'))
        ≡ liftV g (f x) ++ subV (ass* {e} {e'} {e''}) (liftV g ys')
lemma {zero} {e'} {e''} {X} {Y} {Z} g f x [] with f x
... | ys = lemma' {e'} {e''} {X} {Y} {Z} g ys
{-lemma {zero} g f x [] with f x
lemma {zero} g f x [] | [] = refl
lemma {zero} g f x [] | y ∷ ys with g y
lemma {zero} g f x [] | y ∷ ys | [] = {!!}
lemma {zero} g f x [] | y ∷ ys | z ∷ zs = {!!}-}
lemma {suc e} g f x ys' with f x
lemma {suc e} g f x ys' | [] = {!!}
lemma {suc e} g f x (y' ∷ ys') | y ∷ ys = {!!}


mlaw3V : {e e' e'' : M} {X Y Z : Set} (f : X → Vec Y e')
      (g : Y → Vec Z e'') (c : Vec X e) →
      subV (ass* {e} {e'} {e''}) (liftV g (liftV f c))
      ≡ liftV (λ x → liftV g (f x)) c
mlaw3V f g [] = refl
mlaw3V {suc e} {e'} {e''} f g (x ∷ c) =
  begin
    subV (ass* {suc e} {e'} {e''}) (liftV g (liftV f (x ∷ c)))
  ≡⟨ refl ⟩
    subV (ass* {suc e} {e'} {e''}) (liftV g (f x ++ liftV f c))
  ≡⟨ lemma {e} {e'} {e''} g f x (liftV f c) ⟩
    (liftV g (f x) ++ subV (ass* {e} {e'} {e''}) (liftV g (liftV f c)))
  ≡⟨ cong (_++_ (liftV g (f x))) (mlaw3V f g c) ⟩
    liftV g (f x) ++ liftV (λ x → liftV g (f x)) c
  ≡⟨ refl ⟩
    liftV (λ x → liftV g (f x)) (x ∷ c)
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
