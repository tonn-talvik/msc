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
  _⇒_ : Type → Type → Type
  val : Type → Type
  
⟦_⟧ : Type → Set
⟦ nat ⟧ = ℕ
⟦ bool ⟧ = Bool
⟦ t ⇒ u ⟧ = ⟦ t ⟧ → ⟦ u ⟧
⟦ val x ⟧ = ⟦ x ⟧

{- are computation types separate from types?
data Comp : Type → Set where
  val : ∀ {σ} → Comp σ
  -- Type must be bool, how to write that?
  if_then_else_fi : ∀ {σ} → Type → Comp σ → Comp σ → Comp σ
-}

Ctx = List Type

⟦_⟧c : Ctx → Set
⟦ [] ⟧c = ⊤
⟦ σ ∷ Γ ⟧c = ⟦ σ ⟧ × ⟦ Γ ⟧c


infixl 80 _$_
data Term (Γ : Ctx) : Type → Set where
  tt ff : Term Γ bool
  zz : Term Γ nat
  ss : Term Γ nat → Term Γ nat
  val : ∀ {σ} → Term Γ σ → Term Γ σ
  if_then_else_fi : ∀ {σ} → Term Γ bool → Term Γ σ → Term Γ σ → Term Γ σ
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
⟦ val x ⟧t ρ = ⟦ x ⟧t ρ
⟦ if b then m else n fi ⟧t ρ = if ⟦ b ⟧t ρ then ⟦ m ⟧t ρ else ⟦ n ⟧t ρ
⟦ (ss t) ⟧t ρ = suc (⟦ t ⟧t ρ)
⟦ (var x) ⟧t ρ = proj x ρ
⟦ (t $ u) ⟧t ρ = ⟦ t ⟧t ρ (⟦ u ⟧t ρ)
⟦ (lam σ t) ⟧t ρ = λ x → ⟦ t ⟧t (x , ρ)

p1 = ⟦ (var here) $ (var (there here)) ⟧t ( (λ x → x * x) , (3 , top) ) 
p2 = ⟦ ss (ss zz) ⟧t top
p3 = ⟦ if tt then (var here) else (var (there here)) fi ⟧t (1 , (0 , top))
