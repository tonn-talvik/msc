module MyTypeInference where

open import Data.Nat renaming (ℕ to Nat) hiding (erase)
open import Data.List renaming (_∷_ to _::_)
open import Data.Unit
open import Data.Product

open import MyList
open import MyTypes
open import MyExpressions

Cxt = List Type

⟦_⟧c : Cxt → Set
⟦ [] ⟧c = ⊤
⟦ σ :: Γ ⟧c = ⟦ σ ⟧ × ⟦ Γ ⟧c


data Term (Γ : Cxt) : Type -> Set where
  var : forall {τ } -> τ ∈ Γ -> Term Γ τ
  _$_ : forall {σ τ} -> Term Γ (σ ⇒ τ) -> Term Γ σ -> Term Γ τ
  lam : forall σ {τ} -> Term (σ :: Γ) τ -> Term Γ (σ ⇒ τ)


⟦_⟧t : {Γ : Cxt} → {σ : Type} → Term Γ σ → ⟦ Γ ⟧c → ⟦ σ ⟧
⟦ var hd ⟧t ρ = proj₁ ρ
⟦ var (tl x) ⟧t ρ = ⟦ var x ⟧t (proj₂ ρ)
⟦ t $ u ⟧t ρ = (⟦ t ⟧t ρ) (⟦ u ⟧t ρ)
⟦ lam σ t ⟧t ρ =  λ x →  ⟦ t ⟧t ( x , ρ )


erase : forall {Γ τ } -> Term Γ τ -> Raw
erase (var x) = var (index x)
erase (t $ u) = erase t $ erase u
erase (lam σ t) = lam σ (erase t)

data BadTerm (Γ : Cxt) : Set where
  off-scope : Nat -> BadTerm Γ
  _$funbad_ : BadTerm Γ → Raw → BadTerm Γ
  _$funnotfun_ : Term Γ ı → Raw → BadTerm Γ
  _$argbad_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → BadTerm Γ → BadTerm Γ
  _$funargmismatch_/_/ : ∀ {σ τ σ'} → Term Γ (σ ⇒ τ) → Term Γ σ' → σ ≠ σ' → BadTerm Γ
  lambodybad : ∀ σ → BadTerm (σ :: Γ) -> BadTerm Γ

eraseBad : {Γ : Cxt} -> BadTerm Γ -> Raw
eraseBad {Γ} (off-scope n) = var (length Γ + n)
eraseBad (t $funbad e) = eraseBad t $ e
eraseBad (t $funnotfun e) = erase t $ e
eraseBad (t $argbad u) = erase t $ eraseBad u
eraseBad (t $funargmismatch u / r /) = erase t $ erase u
eraseBad (lambodybad σ t) = lam σ (eraseBad t)

data Infer (Γ : Cxt) : Raw -> Set where
  ok : (τ : Type)(t : Term Γ τ ) -> Infer Γ (erase t)
  bad : (b : BadTerm Γ ) -> Infer Γ (eraseBad b)

infer : (Γ : Cxt)(e : Raw) -> Infer Γ e
infer Γ (var n)               with Γ ! n
infer Γ (var .(length Γ + n)) | outside n  = bad (off-scope n)
infer Γ (var .(index x))      | inside σ x = ok σ (var x)
infer Γ (e₁ $ e₂)                      with infer Γ e₁
infer Γ (.(eraseBad t₁) $ e)           | bad t₁  = bad (t₁ $funbad e)
infer Γ (.(erase t₁) $ e₂)             | ok ı t₁ = bad (t₁ $funnotfun e₂)
infer Γ (.(erase t₁) $ e₂)             | ok (σ ⇒ τ) t₁ with infer Γ e₂
infer Γ (.(erase t₁) $ .(eraseBad t₂)) | ok (σ ⇒ τ) t₁ | bad t₂ = bad (t₁ $argbad t₂)
infer Γ (.(erase t₁) $ .(erase t₂))    | ok (σ ⇒ τ) t₁ | ok σ’ t₂ with σ =?= σ’
infer Γ (.(erase t₁) $ .(erase t₂))    | ok (σ ⇒ τ) t₁ | ok .σ t₂ | yes  = ok τ (t₁ $ t₂)
infer Γ (.(erase t₁) $ .(erase t₂))    | ok (σ ⇒ τ) t₁ | ok σ’ t₂ | no r = bad (t₁ $funargmismatch t₂ / r /)
infer Γ (lam σ e)            with infer (σ :: Γ) e
infer Γ (lam σ .(erase t))   | ok τ t = ok (σ ⇒ τ) (lam σ t)
infer Γ (lam σ .(eraseBad t))| bad t  = bad (lambodybad σ t)
