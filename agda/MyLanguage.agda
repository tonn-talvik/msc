module MyLanguage where

open import Data.Nat
open import Data.Bool
open import Data.Unit renaming (tt to top)
open import Data.Product
open import Data.Sum

open import Data.List

data _∈_ {A : Set}(x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)
  
infixr 30 _⇒_
data VType : Set where
  nat : VType
  bool : VType
  _⇒_ : VType → VType → VType
  
⟦_⟧v : VType → Set
⟦ nat ⟧v = ℕ
⟦ bool ⟧v = Bool
⟦ t ⇒ u ⟧v = ⟦ t ⟧v → ⟦ u ⟧v

data CType : VType → Set where
  val : ∀ {σ} → VType → CType σ
  if_then_else_fi : ∀ {σ} → VType → CType σ → CType σ → CType σ

{-
⟦_⟧c : ∀ {σ} → CType σ → Set
⟦ val v ⟧c = ⟦ v ⟧v
⟦ if x then m else n fi ⟧c = {!!}
-}

Ctx = List VType

⟦_⟧l : Ctx → Set
⟦ [] ⟧l = ⊤
⟦ σ ∷ Γ ⟧l = ⟦ σ ⟧v × ⟦ Γ ⟧l

infixl 80 _$_
data VTerm (Γ : Ctx) : VType → Set where
  tt ff : VTerm Γ bool
  zz : VTerm Γ nat
  ss : VTerm Γ nat → VTerm Γ nat
  var : ∀ {τ} → τ ∈ Γ → VTerm Γ τ
  -- how to use CTerm's here? Mutual definition...?
  _$_ : ∀ {σ τ} → VTerm Γ (σ ⇒ τ) → VTerm Γ σ → VTerm Γ τ
  lam : ∀ σ {τ} → VTerm (σ ∷ Γ) τ → VTerm Γ (σ ⇒ τ)


  
data CTerm (Γ : Ctx) : VType → Set where
  val : ∀ {σ} → VTerm Γ σ → CTerm Γ σ
  if_then_else_fi : ∀ {σ} → VTerm Γ bool → CTerm Γ σ → CTerm Γ σ → CTerm Γ σ

proj : {Γ : Ctx} → {σ : VType} → σ ∈ Γ → ⟦ Γ ⟧l → ⟦ σ ⟧v
proj here ρ = proj₁ ρ
proj (there x) ρ = proj x (proj₂ ρ)


⟦_⟧t : {Γ : Ctx} → {σ : VType} → VTerm Γ σ → ⟦ Γ ⟧l → ⟦ σ ⟧v
⟦ tt ⟧t ρ = true
⟦ ff ⟧t ρ = false
⟦ zz ⟧t ρ = zero
⟦ (ss t) ⟧t ρ = suc (⟦ t ⟧t ρ)
⟦ (var x) ⟧t ρ = proj x ρ
⟦ (t $ u) ⟧t ρ = ⟦ t ⟧t ρ (⟦ u ⟧t ρ)
⟦ (lam σ t) ⟧t ρ = λ x → ⟦ t ⟧t (x , ρ)

⟦_⟧ : {Γ : Ctx} → {σ : VType} → CTerm Γ σ → ⟦ Γ ⟧l → ⟦ σ ⟧v
⟦ (val v) ⟧ ρ = ⟦ v ⟧t ρ
⟦ if b then m else n fi ⟧ ρ = (if ⟦ b ⟧t ρ then ⟦ m ⟧ else ⟦ n ⟧) ρ

p1 = ⟦ val (var here) ⟧ (1 , top)
p2 = ⟦ if tt then (val (ss zz)) else val zz fi ⟧ top

{-
p1 = ⟦ (var here) $ (var (there here)) ⟧t ( (λ x → x * x) , (3 , top) ) 
p2 = ⟦ ss (ss zz) ⟧t top
p3 = ⟦ if tt then (var here) else (var (there here)) fi ⟧t (1 , (0 , top))

-}
