module MyLanguage where

open import Relation.Nullary
open import Relation.Binary.Core using (_≡_ ; refl)

open import Data.Nat hiding (_≟_)
open import Data.Bool hiding (T ; _≟_)
open import Data.Empty
open import Data.Unit renaming (tt to top) hiding (_≟_)
open import Data.Product

open import Data.List

open import Finiteness
  hiding (_∈_; here; here'; there)
  renaming (extract to fext)

data _∈_ {A : Set}(x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

data _∈'_ {A : Set} : ℕ → List A → Set where
  here  : ∀ {x xs} → zero ∈' (x ∷ xs)
  there : ∀ {n x xs} → n ∈' xs → suc n ∈' (x ∷ xs)


lookup : {A : Set} → (n : ℕ) → (xs : List A) → n ∈' xs → A
lookup .0 .(x ∷ xs) (here {x} {xs}) = x
lookup .(suc n) .(x ∷ xs) (there {n} {x} {xs} p) = lookup n xs p

lookupcorrect :  {A : Set} → (n : ℕ) → (xs : List A) → (p : n ∈' xs) → lookup n xs p ∈ xs
lookupcorrect .0 .(x ∷ xs) (here {x} {xs}) = here
lookupcorrect .(suc n) .(x ∷ xs) (there {n} {x} {xs} p) = there (lookupcorrect n xs p)

----------------------------------------------------------------------

T : Set → Set
T X = List X

η : {X : Set} → X → T X
η x = [ x ]

lift : {X Y : Set} → (X → T Y) → T X → T Y
lift f []  = []
lift f (x ∷ xs) = f x ++ lift f xs

sfail : {X : Set} → T X
sfail = []

sor : {X : Set} → T X → T X → T X 
sor = _++_

----------------------------------------------------------------------
infixr 30 _⇒_
data VType : Set where
  nat : VType
  bool : VType
  _⇒_ : VType → VType → VType
  _∏_ : VType → VType → VType
  
⟦_⟧v : VType → Set
⟦ nat ⟧v = ℕ
⟦ bool ⟧v = Bool
⟦ t ⇒ u ⟧v = ⟦ t ⟧v → T ⟦ u ⟧v
⟦ t ∏ u ⟧v = ⟦ t ⟧v × ⟦ u ⟧v

----------------------------------------------------------------------

Ctx = List VType

⟦_⟧l : Ctx → Set
⟦ [] ⟧l = ⊤
⟦ σ ∷ Γ ⟧l = ⟦ σ ⟧v × ⟦ Γ ⟧l

----------------------------------------------------------------------

infixl 80 _$_

mutual
  data VTerm (Γ : Ctx) : VType → Set where
    tt ff : VTerm Γ bool
    zz : VTerm Γ nat
    ss : VTerm Γ nat → VTerm Γ nat
    ⟨_,_⟩ : ∀ {σ τ} → VTerm Γ σ → VTerm Γ τ → VTerm Γ (σ ∏ τ)
    fst : ∀ {σ τ} → VTerm Γ (σ ∏ τ) → VTerm Γ σ
    snd : ∀ {σ τ} → VTerm Γ (σ ∏ τ) → VTerm Γ τ
    var : ∀ {τ} → τ ∈ Γ → VTerm Γ τ
    lam : ∀ σ {τ} → CTerm (σ ∷ Γ) τ → VTerm Γ (σ ⇒ τ)
    
  data CTerm (Γ : Ctx) : VType → Set where
    val : ∀ {σ} → VTerm Γ σ → CTerm Γ σ
    fail : ∀ {σ} → CTerm Γ σ
    choose : ∀ {σ} → CTerm Γ σ → CTerm Γ σ → CTerm Γ σ
    if_then_else_fi : ∀ {σ} → VTerm Γ bool → CTerm Γ σ → CTerm Γ σ → CTerm Γ σ
    _$_ : ∀ {σ τ} → VTerm Γ (σ ⇒ τ) → VTerm Γ σ → CTerm Γ τ
    prec : ∀ {σ} → VTerm Γ nat →
           CTerm Γ σ →
           CTerm (σ ∷ nat ∷ Γ) σ → CTerm Γ σ
    LET_IN_ : ∀ {σ τ} → CTerm Γ σ → CTerm (σ ∷ Γ) τ → CTerm Γ τ

proj : {Γ : Ctx} → {σ : VType} → σ ∈ Γ → ⟦ Γ ⟧l → ⟦ σ ⟧v
proj here ρ = proj₁ ρ
proj (there x) ρ = proj x (proj₂ ρ)


primrec : {t : Set} → ℕ → t → (ℕ → t → t) → t
primrec zero z s = z
primrec (suc n) z s = s n (primrec n z s)

primrecT : {t : Set} → ℕ → T t → (ℕ → t → T t) → T t
primrecT zero z s = z
primrecT (suc n) z s = lift (s n) (primrecT n z s)

----------------------------------------------------------------------
mutual
  ⟦_⟧t : {Γ : Ctx} → {σ : VType} → VTerm Γ σ → ⟦ Γ ⟧l → ⟦ σ ⟧v
  ⟦ tt ⟧t ρ = true
  ⟦ ff ⟧t ρ = false
  ⟦ zz ⟧t ρ = zero
  ⟦ ss t ⟧t ρ = suc (⟦ t ⟧t ρ)
  ⟦ ⟨ t , u ⟩ ⟧t ρ = ⟦ t ⟧t ρ , ⟦ u ⟧t ρ
  ⟦ fst p ⟧t ρ = proj₁ (⟦ p ⟧t ρ)
  ⟦ snd p ⟧t ρ = proj₂ (⟦ p ⟧t ρ)
  ⟦ var x ⟧t ρ = proj x ρ
  ⟦ lam σ t ⟧t ρ = λ x → ⟦ t ⟧ (x , ρ)
  
  ⟦_⟧ : {Γ : Ctx} → {σ : VType} → CTerm Γ σ → ⟦ Γ ⟧l → T ⟦ σ ⟧v
  ⟦ val v ⟧ ρ = η (⟦ v ⟧t ρ)
  ⟦ fail ⟧ ρ = sfail
  ⟦ choose t u ⟧ ρ = sor (⟦ t ⟧ ρ) (⟦ u ⟧ ρ)
  ⟦ if b then m else n fi ⟧ ρ = (if ⟦ b ⟧t ρ then ⟦ m ⟧ else ⟦ n ⟧) ρ
  ⟦ prec v m n ⟧ ρ = primrecT (⟦ v ⟧t ρ) (⟦ m ⟧ ρ) (λ x → λ y → ⟦ n ⟧ (y , x , ρ))
  ⟦ t $ u ⟧ ρ = ⟦ t ⟧t ρ (⟦ u ⟧t ρ)

  ⟦ LET m IN n ⟧ ρ = lift (λ x → ⟦ n ⟧ (x , ρ)) (⟦ m ⟧ ρ)

----------------------------------------------------------------------

natify : ∀ {Γ} → ℕ → VTerm Γ nat
natify zero = zz
natify (suc n) = ss (natify n)

-- binary relations are inequal, if there are pointwise inequalities
lemma-⇒-1 : (u₁ u₂ v₁ v₂ : VType) → ¬ u₁ ≡ v₁ → ¬ (u₁ ⇒ u₂ ≡ v₁ ⇒ v₂)
lemma-⇒-1 u₁ u₂ .u₁ .u₂ ¬q refl = ¬q refl

lemma-⇒-2 : (u₁ u₂ v₁ v₂ : VType) → ¬ u₂ ≡ v₂ → ¬ (u₁ ⇒ u₂ ≡ v₁ ⇒ v₂)
lemma-⇒-2 u₁ u₂ .u₁ .u₂ ¬q refl = ¬q refl

lemma-∏-1 : (u₁ u₂ v₁ v₂ : VType) → ¬ u₁ ≡ v₁ → ¬ (u₁ ∏ u₂ ≡ v₁ ∏ v₂)
lemma-∏-1 u₁ u₂ .u₁ .u₂ ¬q refl = ¬q refl

lemma-∏-2 : (u₁ u₂ v₁ v₂ : VType) → ¬ u₂ ≡ v₂ → ¬ (u₁ ∏ u₂ ≡ v₁ ∏ v₂)
lemma-∏-2 u₁ u₂ .u₁ .u₂ ¬q refl = ¬q refl

-- is ALL of this really required?
_≟_ : (u v : VType) → Dec (u ≡ v)
nat ≟ nat      = yes refl
nat ≟ bool     = no (λ ())
nat ≟ u ⇒ v    = no (λ ())
nat ≟ (u ∏ v)  = no (λ ())
bool ≟ nat     = no (λ ())
bool ≟ bool    = yes refl
bool ≟ u ⇒ v   = no (λ ())
bool ≟ (u ∏ v) = no (λ ())
u ⇒ u₁ ≟ nat = no (λ ())
u ⇒ u₁ ≟ bool = no (λ ())
u₁ ⇒ u₂ ≟ v₁ ⇒ v₂ with u₁ ≟ v₁ | u₂ ≟ v₂
u₁ ⇒ u₂ ≟ v₁ ⇒ v₂ | yes p | yes q rewrite p | q = yes refl
u₁ ⇒ u₂ ≟ v₁ ⇒ v₂ | yes p | no ¬q = no (lemma-⇒-2 u₁ u₂ v₁ v₂ ¬q)
u₁ ⇒ u₂ ≟ v₁ ⇒ v₂ | no ¬p | q = no (lemma-⇒-1 u₁ u₂ v₁ v₂ ¬p)
u₁ ⇒ u₂ ≟ (v₁ ∏ v₂) = no (λ ())
(u ∏ v) ≟ nat = no (λ ())
(u ∏ v) ≟ bool = no (λ ())
(u₁ ∏ u₂) ≟ v₁ ⇒ v₂ = no (λ ())
(u₁ ∏ u₂) ≟ (v₁ ∏ v₂) with u₁ ≟ v₁ | u₂ ≟ v₂
(u₁ ∏ u₂) ≟ (v₁ ∏ v₂) | yes p | yes q rewrite p | q = yes refl
(u₁ ∏ u₂) ≟ (v₁ ∏ v₂) | yes p | no ¬q = no (lemma-∏-2 u₁ u₂ v₁ v₂ ¬q)
(u₁ ∏ u₂) ≟ (v₁ ∏ v₂) | no ¬p | yes q = no (lemma-∏-1 u₁ u₂ v₁ v₂ ¬p)
(u₁ ∏ u₂) ≟ (v₁ ∏ v₂) | no ¬p | no ¬q = no (lemma-∏-1 u₁ u₂ v₁ v₂ ¬p) -- duplicates previous line

lemma-∉ : (u v : VType) → (Γ : Ctx) → ¬ u ≡ v → ¬ u ∈ Γ → ¬ u ∈ (v ∷ Γ)
lemma-∉ u .u g ¬p ¬q here = ¬p refl
lemma-∉ u v g ¬p ¬q (there r) = ¬q r

_∈?_ : (v : VType) → (Γ : Ctx) → Dec (v ∈ Γ)
v ∈? [] = no (λ ()) -- auto
u ∈? (v ∷ Γ) with u ≟ v
u ∈? (v ∷ Γ) | yes p rewrite p = yes here
u ∈? (v ∷ Γ) | no ¬p with u ∈? Γ
u ∈? (v ∷ Γ) | no ¬p | yes q = yes (there q)
u ∈? (v ∷ Γ) | no ¬p | no ¬q = no (lemma-∉ u v Γ ¬p ¬q)

lemma-∉' : {Γ : Ctx} → {τ : VType} → (v : ℕ) → ¬ v ∈' Γ → ¬ suc v ∈' (τ ∷ Γ)
lemma-∉' n p (there q) = p q

_∈'?_ : (v : ℕ) → (Γ : Ctx) → Dec (v ∈' Γ)
v ∈'? [] = no (λ ())
zero ∈'? (x ∷ Γ) = yes here
suc v ∈'? (x ∷ Γ) with v ∈'? Γ 
suc v ∈'? (x ∷ Γ) | yes p =  yes (there p)
suc v ∈'? (x ∷ Γ) | no ¬p =  no (lemma-∉' v ¬p)

gamma = nat ∷ nat ∷ bool ∷ bool ∏ nat ∷ []
g1 = nat ∈? gamma
g2 = nat ⇒ bool ∈? gamma
g3 = (bool ∏ nat) ∈? gamma


extract : {P : Set} → {d : Dec P} → truncate d → P
extract {_} {yes p} t = p
extract {_} {no ¬p} ()

data ScopedVar (Γ : Ctx) : Set where
  svar : (v : ℕ) → {_ : truncate (v ∈'? Γ)} → ScopedVar Γ


svar2var : {Γ : Ctx} → ScopedVar Γ → VType
svar2var (svar v {p}) = lookup v _ ( extract p) 

svar2inlist : {Γ : Ctx} → (sv : ScopedVar Γ) → svar2var sv ∈ Γ
svar2inlist (svar v {p}) = lookupcorrect v _ (extract p)


war = svar2inlist {gamma} (svar 0)
war-contra = svar2inlist {gamma} (svar 5)

varify : {Γ : Ctx} → (v : ℕ) → {p : truncate (v ∈'? Γ)} → VTerm Γ (svar2var (svar v {p}))
varify v {p} = var (svar2inlist (svar v {p} ))

pv0        = ⟦ val (lam nat (val (varify 0))) ⟧ top
-- pv0-contra = ⟦ val (lam nat (val (varify 1))) ⟧ top
pv1        = ⟦ val (varify 0) ⟧ (1 , top)
-- pv1-contra = ⟦ val (varify 1) ⟧ (1 , top)
pv2        = ⟦ if (varify 2) then val (varify 0) else val (varify 1) fi ⟧ (1 , 2 , false , top)
pv3 : {Γ : Ctx} → ⟦ nat ∷ Γ ⟧l →  T ℕ
pv3        = ⟦ val (varify 0) ⟧

-- http://mazzo.li/posts/Lambda.html builds variable proofs during type checking
-- data Syntax : Set where
--   var : ℕ → Syntax
-- data Term {n} {Γ : Ctx n) : Type → Set where
--   var : ∀ {τ} (v : Fin n) → τ ≡ lookup v Γ → Term Γ τ

----------------------------------------------------------------------

p1 = ⟦ val (var here) ⟧ (1 , top)
p2 = ⟦ if tt then (val (ss zz)) else val zz fi ⟧ top
p3 = ⟦ (var here) $ (var (there here)) ⟧ ( (λ x → η (x * x)) , (3 , top) ) 
p4 = ⟦ val (snd ⟨ zz , tt ⟩ ) ⟧ top
p5 = ⟦ lam nat (val (ss (var here))) $ zz ⟧ top
p6 = ⟦ prec (natify 6) (val zz) ((LET val (var here) IN (val (var (there here))) )) ⟧ top
p7 : ℕ → T ℕ
p7 n  = ⟦ prec (natify n) (val zz) (choose (val (var here)) (val (ss (ss (var here))))) ⟧ top

add : ∀ {Γ} → VTerm Γ (nat ⇒ nat ⇒ nat)
add = (lam nat (
          val (lam nat
               (prec (var here)
                     (val (var (there here)))
                     (val (ss (var here)))))))
p-add-3-4 = ⟦ LET add $ var (there here) IN var here $ var (there here) ⟧ (3 , (4 , top))

mul : ∀ {Γ} → VTerm Γ (nat ⇒ nat ⇒ nat)
mul = (lam nat (
          val (lam nat
               (prec (var here)
                     (val zz)
                     (LET add $ var here IN
                          (
                               ( var here
                                    $ var (there (there (there (there here)))))))))))
p-mul-3-4 = ⟦ LET mul $ natify 3 IN var here $ natify 4 ⟧ top
