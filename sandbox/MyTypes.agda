module MyTypes where

infixr 30 _⇒_
data Type : Set where
  ı : Type
  _⇒_ : Type -> Type -> Type

data _≠_ : Type -> Type -> Set where
  base-not-func : {σ τ : Type} →  ı ≠ σ ⇒ τ
  func-not-base : {σ τ : Type} → σ ⇒ τ  ≠  ı 
  diff-result   : {σ τ₁ τ₂ : Type} → τ₁ ≠ τ₂ → (σ ⇒ τ₁) ≠ (σ ⇒ τ₂)
  diff-argument : {σ₁ σ₂ τ : Type} → σ₁ ≠ σ₂ → (σ₁ ⇒ τ) ≠ (σ₂ ⇒ τ)
  diff-func : {σ₁ σ₂ τ₁ τ₂ : Type} → σ₁ ≠ σ₂ → τ₁ ≠ τ₂ → (σ₁ ⇒ τ₁) ≠ (σ₂ ⇒ τ₂)

data Equal? : Type -> Type -> Set where
  yes : forall {τ} -> Equal? τ τ
  no  : forall {σ τ} -> σ ≠ τ -> Equal? σ τ

_=?=_ : (σ τ : Type) -> Equal? σ τ
ı          =?= ı          = yes
ı          =?= (τ₁ ⇒ τ₂) = no base-not-func
(τ₁ ⇒ τ₂) =?= ı          = no func-not-base
(σ₁ ⇒ τ₁) =?= (σ₂ ⇒ τ₂) with σ₁ =?= σ₂ | τ₁ =?= τ₂
(σ ⇒ τ)   =?= (.σ ⇒ .τ) | yes  | yes  = yes
(σ ⇒ τ₁)  =?= (.σ ⇒ τ₂) | yes  | no r = no (diff-result r)
(σ₁ ⇒ τ)  =?= (σ₂ ⇒ .τ) | no a | yes  = no (diff-argument a)
(σ₁ ⇒ τ₁) =?= (σ₂ ⇒ τ₂) | no a | no r = no (diff-func a r)


