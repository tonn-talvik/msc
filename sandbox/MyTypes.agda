module MyTypes where

infixr 30 _⇒_ _∏_
data Type : Set where
  ı : Type
  _⇒_ : Type → Type → Type
  _∏_ : Type → Type → Type

data _≠_ : Type → Type → Set where
  base-not-func : {σ τ : Type}     →      ı ≠ σ ⇒ τ
  base-not-prod : {σ τ : Type}     →      ı ≠ σ ∏ τ
  func-not-base : {σ τ : Type}     → σ ⇒ τ ≠ ı 
  func-not-prod : {σ τ π ρ : Type} → σ ⇒ τ ≠ π ∏ ρ
  prod-not-base : {π ρ : Type}     →  π ∏ ρ ≠ ı
  prod-not-func : {σ τ π ρ : Type} →  π ∏ ρ ≠ σ ⇒ τ
  diff-result   : {σ τ₁ τ₂ : Type} → τ₁ ≠ τ₂ → (σ ⇒ τ₁) ≠ (σ ⇒ τ₂)
  diff-argument : {σ₁ σ₂ τ : Type} → σ₁ ≠ σ₂ → (σ₁ ⇒ τ) ≠ (σ₂ ⇒ τ)
  diff-func : {σ₁ σ₂ τ₁ τ₂ : Type} → σ₁ ≠ σ₂ → τ₁ ≠ τ₂ → (σ₁ ⇒ τ₁) ≠ (σ₂ ⇒ τ₂)
  diff-fst  : {π₁ π₂ ρ₁ ρ₂ : Type} → π₁ ≠ π₂ → (π₁ ∏ ρ₁) ≠ (π₂ ∏ ρ₂)
  diff-snd  : {π₁ π₂ ρ₁ ρ₂ : Type} → ρ₁ ≠ ρ₂ → (π₁ ∏ ρ₁) ≠ (π₂ ∏ ρ₂)
  diff-prod : {π₁ π₂ ρ₁ ρ₂ : Type} → π₁ ≠ π₂ → ρ₁ ≠ ρ₂ → (π₁ ∏ ρ₁) ≠ (π₂ ∏ ρ₂)

data Equal? : Type → Type → Set where
  yes : forall {τ} → Equal? τ τ
  no  : forall {σ τ} → σ ≠ τ → Equal? σ τ

_=?=_ : (σ τ : Type) → Equal? σ τ
ı          =?= ı          = yes
ı          =?= (_ ⇒ _)   = no base-not-func
ı          =?= (_ ∏ _)    = no base-not-prod
(_ ⇒ _)   =?= ı          = no func-not-base
(_ ⇒ _)   =?= (_ ∏ _)    = no func-not-prod
(_ ∏ _)    =?= ı          = no prod-not-base
(_ ∏ _)    =?= (_ ⇒ _)   = no prod-not-func
(π₁ ∏ ρ₁)  =?= (π₂ ∏ ρ₂) with π₁ =?= π₂ | ρ₁ =?= ρ₂
.π₂ ∏ .ρ₂  =?= π₂ ∏ ρ₂      | yes       | yes      = yes
.π₂ ∏ ρ₁   =?= π₂ ∏ ρ₂      | yes       | no s     = no (diff-snd s)
π₁ ∏ .ρ₂   =?= π₂ ∏ ρ₂      | no f      | yes      = no (diff-fst f)
π₁ ∏ ρ₁    =?= π₂ ∏ ρ₂      | no f      | no s     = no (diff-prod f s)
(σ₁ ⇒ τ₁) =?= (σ₂ ⇒ τ₂) with σ₁ =?= σ₂ | τ₁ =?= τ₂
(σ ⇒ τ)   =?= (.σ ⇒ .τ)    | yes       | yes      = yes
(σ ⇒ τ₁)  =?= (.σ ⇒ τ₂)    | yes       | no r     = no (diff-result r)
(σ₁ ⇒ τ)  =?= (σ₂ ⇒ .τ)    | no a      | yes      = no (diff-argument a)
(σ₁ ⇒ τ₁) =?= (σ₂ ⇒ τ₂)    | no a      | no r     = no (diff-func a r)


