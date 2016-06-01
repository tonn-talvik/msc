module MyLanguage where

open import Data.Nat
open import Data.Bool
open import Data.Unit renaming (tt to top)
open import Data.Product
open import Data.Char

open import Data.List

data _∈_ {A : Set}(x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

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
⟦ t ⇒ u ⟧v = ⟦ t ⟧v → ⟦ u ⟧v
⟦ t ∏ u ⟧v = ⟦ t ⟧v × ⟦ u ⟧v

----------------------------------------------------------------------

Ctx = List VType

⟦_⟧l : Ctx → Set
⟦ [] ⟧l = ⊤
⟦ σ ∷ Γ ⟧l = ⟦ σ ⟧v × ⟦ Γ ⟧l

----------------------------------------------------------------------

infixl 80 _$_
data VTerm (Γ : Ctx) : VType → Set where
  tt ff : VTerm Γ bool
  zz : VTerm Γ nat
  ss : VTerm Γ nat → VTerm Γ nat
  ⟨_,_⟩ : ∀ {σ τ} → VTerm Γ σ → VTerm Γ τ → VTerm Γ (σ ∏ τ)
  fst : ∀ {σ τ} → VTerm Γ (σ ∏ τ) → VTerm Γ σ
  snd : ∀ {σ τ} → VTerm Γ (σ ∏ τ) → VTerm Γ τ
  var : ∀ {τ} → τ ∈ Γ → VTerm Γ τ

  
data CTerm (Γ : Ctx) : VType → Set where
  val : ∀ {σ} → VTerm Γ σ → CTerm Γ σ
  if_then_else_fi : ∀ {σ} → VTerm Γ bool → CTerm Γ σ → CTerm Γ σ → CTerm Γ σ
  _$_ : ∀ {σ τ} → CTerm Γ (σ ⇒ τ) → VTerm Γ σ → CTerm Γ τ
  lam : ∀ σ {τ} → CTerm (σ ∷ Γ) τ → CTerm Γ (σ ⇒ τ)
  prec : ∀ {σ} → VTerm Γ nat →
         CTerm Γ σ →
         CTerm Γ (nat ⇒ σ ⇒ σ) → CTerm Γ σ
  LET_⇐_IN_ : ∀ {σ τ} → Char → CTerm Γ σ → CTerm (σ ∷ Γ) τ → CTerm Γ τ

proj : {Γ : Ctx} → {σ : VType} → σ ∈ Γ → ⟦ Γ ⟧l → ⟦ σ ⟧v
proj here ρ = proj₁ ρ
proj (there x) ρ = proj x (proj₂ ρ)


⟦_⟧t : {Γ : Ctx} → {σ : VType} → VTerm Γ σ → ⟦ Γ ⟧l → ⟦ σ ⟧v
⟦ tt ⟧t ρ = true
⟦ ff ⟧t ρ = false
⟦ zz ⟧t ρ = zero
⟦ ss t ⟧t ρ = suc (⟦ t ⟧t ρ)
⟦ ⟨ t , u ⟩ ⟧t ρ = ⟦ t ⟧t ρ , ⟦ u ⟧t ρ
⟦ fst p ⟧t ρ = proj₁ (⟦ p ⟧t ρ)
⟦ snd p ⟧t ρ = proj₂ (⟦ p ⟧t ρ)
⟦ var x ⟧t ρ = proj x ρ


primrec : {t : Set} → ℕ → t → (ℕ → t → t) → t
primrec zero z s = z
primrec (suc n) z s = s (suc n) (primrec n z s)

⟦_⟧ : {Γ : Ctx} → {σ : VType} → CTerm Γ σ → ⟦ Γ ⟧l → ⟦ σ ⟧v
⟦ val v ⟧ ρ = ⟦ v ⟧t ρ
⟦ if b then m else n fi ⟧ ρ = (if ⟦ b ⟧t ρ then ⟦ m ⟧ else ⟦ n ⟧) ρ
⟦ (prec v m n) ⟧ ρ = primrec (⟦ v ⟧t ρ) (⟦ m ⟧ ρ) (⟦ n ⟧ ρ)
⟦ t $ u ⟧ ρ = ⟦ t ⟧ ρ (⟦ u ⟧t ρ)
⟦ lam σ t ⟧ ρ = λ x → ⟦ t ⟧ (x , ρ)
⟦ LET c ⇐ m IN n ⟧ ρ = ⟦ n ⟧ ((⟦ m ⟧ ρ) , ρ)

----------------------------------------------------------------------

natify : ∀ {Γ} → ℕ → VTerm Γ nat
natify zero = zz
natify (suc n) = ss (natify n)


p1 = ⟦ val (var here) ⟧ (1 , top)
p2 = ⟦ if tt then (val (ss zz)) else val zz fi ⟧ top
p3 = ⟦ (val (var here)) $ (var (there here)) ⟧ ( (λ x → x * x) , (3 , top) ) 
p4 = ⟦ val (snd ⟨ zz , tt ⟩ ) ⟧ top
p5 = ⟦ lam nat (val (ss (var here))) $ zz ⟧ top
p6 = ⟦ prec (natify 6) (val zz) (lam nat (LET 'x' ⇐ val (var here) IN lam nat (val (var (there here))) )) ⟧ top


add : ∀ {Γ} → CTerm Γ (nat ⇒ nat ⇒ nat)
add = lam nat
          (lam nat
               (prec (var here)
                     (val (var (there here)))
                     (lam nat (lam nat (val (ss (var here)))))))

mul : ∀ {Γ} → CTerm Γ (nat ⇒ nat ⇒ nat)
mul = lam nat
          (lam nat
               (prec (var here)
                     (val zz)
                     (lam nat
                          (lam nat
                               (LET 'x' ⇐ add $ var here
                                              $ var (there (there (there here)))
                                    IN val (var here))))))

fact : ∀ {Γ} → CTerm Γ (nat ⇒ nat)
fact = lam nat
           (prec (var here)
                 (val (ss zz))
                 (lam nat
                      (lam nat
                           (LET 'x' ⇐ mul $ var here $ var (there here)
                                IN val (var here)))))

p-add-3-4 = ⟦ add $ var here $ var (there here) ⟧ (3 , (4 , top))
p-mul-3-4 = ⟦ mul $ natify 3 $ natify 4 ⟧ top
p-fact-5 = ⟦ fact $ natify 5 ⟧ top
