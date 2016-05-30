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
data ValueType : Set where
  nat : ValueType
  bool : ValueType
  _⇒_ : ValueType → ValueType → ValueType
  
⟦_⟧v : ValueType → Set
⟦ nat ⟧v = ℕ
⟦ bool ⟧v = Bool
⟦ t ⇒ u ⟧v = ⟦ t ⟧v → ⟦ u ⟧v

data CompType : ValueType → Set where
  val : ∀ {σ} → ValueType → CompType σ
  if_then_else_fi : ∀ {σ} → bool → CompType σ → CompType σ → CompType σ

⟦_⟧c : ∀ {σ} → CompType σ → Set
⟦ val v ⟧c = ⟦ v ⟧v
⟦ if x then m else n fi ⟧c = {!!}
--⟦ val v ⟧c = ⟦ v ⟧v

Type = ∀ {σ} → ValueType ⊎ CompType σ

⟦_⟧ : Type → Set
⟦ t ⟧ = {!!}
--⟦ inj₁ v ⟧ = ⟦ v ⟧v
--⟦ inj₂ c ⟧ = ⟦ c ⟧c

{- are computation types separate from types?
data Comp : Type → Set where
  val : ∀ {σ} → Comp σ
  -- Type must be bool, how to write that?
  
-}

Ctx = List Type

⟦_⟧l : Ctx → Set
⟦ [] ⟧l = ⊤
⟦ σ ∷ Γ ⟧l = ⟦ σ ⟧ × ⟦ Γ ⟧l


infixl 80 _$_
data Term (Γ : Ctx) : Type → Set where
  tt ff : Term Γ (inj₁ bool)
  zz : Term Γ (inj₁ nat)
  ss : Term Γ (inj₁ nat) → Term Γ (inj₁ nat)
--  val : ∀ {σ} → Term Γ (inj₁ σ) → Term Γ (inj₂ σ)
--  if_then_else_fi : ∀ {σ} → Term Γ (inj₁ bool) → Term Γ σ → Term Γ σ → Term Γ σ
  var : ∀ {τ} → τ ∈ Γ → Term Γ τ
  _$_ : ∀ {σ τ} → Term Γ (inj₁ (σ ⇒ τ)) → Term Γ (inj₁ σ) → Term Γ (inj₁ τ)
  lam : ∀ σ {τ} → Term ((inj₁ σ) ∷ Γ) (inj₁ τ) → Term Γ (inj₁ (σ ⇒ τ))

{-proj : {Γ : Ctx} → {σ : ValueType} → inj₁ σ ∈ Γ → ⟦ Γ ⟧l → ⟦ σ ⟧v
proj here (value , comp) = value
--proj (there p) ρ = {!!}
--proj here ρ = proj₁ ρ
proj (there x) ρ = proj x (proj₂ ρ)
-}

{-
⟦_⟧t : {Γ : Ctx} → {σ : Type} → Term Γ σ → ⟦ Γ ⟧c → ⟦ σ ⟧v
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
-}
