module MyTypeInference where

open import Data.Nat renaming (ℕ to Nat; _*_ to _n*_)
open import Data.List renaming (_∷_ to _::_)

open import MyList
open import MyTypes
open import MyExpressions

Cxt = List Type

data Term (Γ : Cxt) : Type → Set where
  var : forall {τ } → τ ∈ Γ → Term Γ τ
  _$_ : forall {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : forall σ {τ} → Term (σ :: Γ) τ → Term Γ (σ ⇒ τ)
  _*_ : forall {π ρ} → Term Γ π → Term Γ ρ → Term Γ (π ∏ ρ)
  fst : forall {π ρ} → Term Γ (π ∏ ρ) → Term Γ π
  snd : forall {π ρ} → Term Γ (π ∏ ρ) → Term Γ ρ

erase : forall {Γ τ } → Term Γ τ → Raw
erase (var x) = var (index x)
erase (t $ u) = erase t $ erase u
erase (lam σ t) = lam σ (erase t)
erase (p * r) = erase p * erase r
erase (fst t) = fst (erase t)
erase (snd t) = snd (erase t)

data BadTerm (Γ : Cxt) : Set where
  off-scope : Nat → BadTerm Γ
  _$funbad_ : BadTerm Γ → Raw → BadTerm Γ
  _$var-not-fun_ : Term Γ ı → Raw → BadTerm Γ
  _$argbad_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → BadTerm Γ → BadTerm Γ
  _$funargmismatch_/_/ : ∀ {σ τ σ'} → Term Γ (σ ⇒ τ) → Term Γ σ' → σ ≠ σ' → BadTerm Γ
  _$prod-not-fun_ : ∀ {π ρ} → Term Γ (π ∏ ρ) → Raw → BadTerm Γ
  lambodybad : ∀ σ → BadTerm (σ :: Γ) → BadTerm Γ
  _*fst-bad_ : BadTerm Γ → Raw → BadTerm Γ
  _*snd-bad_ : ∀ {π} → Term Γ π → BadTerm Γ → BadTerm Γ
  fst-non-prod : ∀ {τ} → Term Γ τ → BadTerm Γ
  fst-bad : BadTerm Γ → BadTerm Γ
  snd-non-prod : ∀ {τ} → Term Γ τ → BadTerm Γ
  snd-bad : BadTerm Γ → BadTerm Γ


eraseBad : {Γ : Cxt} → BadTerm Γ → Raw
eraseBad {Γ} (off-scope n) = var (length Γ + n)
eraseBad (t $funbad e) = eraseBad t $ e
eraseBad (t $var-not-fun e) = erase t $ e
eraseBad (t $argbad u) = erase t $ eraseBad u
eraseBad (t $funargmismatch u / r /) = erase t $ erase u
eraseBad (lambodybad σ t) = lam σ (eraseBad t)
eraseBad (f *fst-bad s) = eraseBad f * s
eraseBad (f *snd-bad s) = erase f * eraseBad s
eraseBad (p $prod-not-fun t) = erase p $ t
eraseBad (fst-non-prod t) = fst (erase t)
eraseBad (fst-bad t) = fst (eraseBad t)
eraseBad (snd-non-prod t) = snd (erase t)
eraseBad (snd-bad t) = snd (eraseBad t)

data Infer (Γ : Cxt) : Raw → Set where
  ok : (τ : Type)(t : Term Γ τ ) → Infer Γ (erase t)
  bad : (b : BadTerm Γ ) → Infer Γ (eraseBad b)

infer : (Γ : Cxt)(e : Raw) → Infer Γ e
infer Γ (var n)               with Γ ! n
infer Γ (var .(length Γ + n)) | outside n  = bad (off-scope n)
infer Γ (var .(index x))      | inside σ x = ok σ (var x)
infer Γ (e₁ $ e₂)                      with infer Γ e₁
infer Γ (.(eraseBad t₁) $ e)           | bad t₁  = bad (t₁ $funbad e)
infer Γ (.(erase t₁) $ e₂)             | ok ı t₁ = bad (t₁ $var-not-fun e₂)
infer Γ (.(erase t₁) $ e₂)             | ok (π ∏ ρ) t₁ = bad (t₁ $prod-not-fun e₂)
infer Γ (.(erase t₁) $ e₂)             | ok (σ ⇒ τ) t₁ with infer Γ e₂
infer Γ (.(erase t₁) $ .(eraseBad t₂)) | ok (σ ⇒ τ) t₁ | bad t₂ = bad (t₁ $argbad t₂)
infer Γ (.(erase t₁) $ .(erase t₂))    | ok (σ ⇒ τ) t₁ | ok σ’ t₂ with σ =?= σ’
infer Γ (.(erase t₁) $ .(erase t₂))    | ok (σ ⇒ τ) t₁ | ok .σ t₂ | yes  = ok τ (t₁ $ t₂)
infer Γ (.(erase t₁) $ .(erase t₂))    | ok (σ ⇒ τ) t₁ | ok σ’ t₂ | no r = bad (t₁ $funargmismatch t₂ / r /)
infer Γ (lam σ e)            with infer (σ :: Γ) e
infer Γ (lam σ .(erase t))   | ok τ t = ok (σ ⇒ τ) (lam σ t)
infer Γ (lam σ .(eraseBad t))| bad t  = bad (lambodybad σ t)
infer Γ (p * r)                      with infer Γ p 
infer Γ (.(erase t) * r)             | ok τ t with infer Γ r
infer Γ (.(erase t) * .(erase u))    | ok π t | ok ρ u = ok (π ∏ ρ) (t * u)
infer Γ (.(erase t) * .(eraseBad b)) | ok τ t | bad b = bad (t *snd-bad b)
infer Γ (.(eraseBad b) * r)          | bad b = bad (b *fst-bad r)
infer Γ (fst t) with infer Γ t
infer Γ (fst .(erase t)) | ok ı t = bad (fst-non-prod t)
infer Γ (fst .(erase t)) | ok (τ ⇒ τ₁) t = bad (fst-non-prod t)
infer Γ (fst .(erase t)) | ok (π ∏ ρ) t = ok π (fst t)
infer Γ (fst .(eraseBad b)) | bad b = bad (fst-bad b)
infer Γ (snd t) with infer Γ t
infer Γ (snd .(erase t)) | ok ı t = bad (snd-non-prod t)
infer Γ (snd .(erase t)) | ok (τ ⇒ τ₁) t = bad (snd-non-prod t)
infer Γ (snd .(erase t)) | ok (π ∏ ρ) t = ok ρ (snd t)
infer Γ (snd .(eraseBad b)) | bad b = bad (snd-bad b)

