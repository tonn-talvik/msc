module MyLanguage where

open import Data.Nat
open import Data.Bool hiding (T)
open import Data.Unit renaming (tt to top)
open import Data.Product

open import Data.List

data _∈_ {A : Set}(x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

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
