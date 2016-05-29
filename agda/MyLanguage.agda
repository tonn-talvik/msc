module MyLanguage where

open import Data.Nat
open import Data.Bool
open import Data.Unit renaming (tt to top)
open import Data.Product

open import Data.List

data _∈_ {A : Set}(x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)
  
infixr 30 _⇒_
data Type : Set where
  nat : Type
  bool : Type
  _⇒_ : Type -> Type -> Type
  
⟦_⟧ : Type → Set
⟦ nat ⟧ = ℕ
⟦ bool ⟧ = Bool
⟦ t ⇒ u ⟧ = ⟦ t ⟧ → ⟦ u ⟧


infixl 80 _$_

Ctx = List Type

⟦_⟧c : Ctx → Set
⟦ [] ⟧c = ⊤
⟦ σ ∷ Γ ⟧c = ⟦ σ ⟧ × ⟦ Γ ⟧c

data Term (Γ : Ctx) : Type → Set where
  tt ff : Term Γ bool
  zz : Term Γ nat
  ss : Term Γ nat → Term Γ nat
  var : ∀ {τ} → τ ∈ Γ → Term Γ τ
  _$_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

proj : {Γ : Ctx} → {σ : Type} → σ ∈ Γ → ⟦ Γ ⟧c → ⟦ σ ⟧
proj here ρ = proj₁ ρ
proj (there x) ρ = proj x (proj₂ ρ)

⟦_⟧t : {Γ : Ctx} → {σ : Type} → Term Γ σ → ⟦ Γ ⟧c → ⟦ σ ⟧
⟦ tt ⟧t ρ = true
⟦ ff ⟧t ρ = false
⟦ zz ⟧t ρ = zero
⟦ (ss t) ⟧t ρ = suc (⟦ t ⟧t ρ)
⟦ (var x) ⟧t ρ = proj x ρ
⟦ (t $ u) ⟧t ρ = ⟦ t ⟧t ρ (⟦ u ⟧t ρ)
⟦ (lam σ t) ⟧t ρ = λ x → ⟦ t ⟧t (x , ρ)

p1 = ⟦ (var here) $ (var (there here)) ⟧t ( (λ x → x * x) , (3 , top) ) 
p2 = ⟦ ss (ss zz) ⟧t top
