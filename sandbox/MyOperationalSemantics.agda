module MyOperationalSemantics where

open import Data.Nat renaming (ℕ to Nat)
open import Data.List renaming (_∷_ to _::_)

open import MyTypes
open import MyExpressions
open import MyTypeInference

----------------------------------------------------------------

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Bool renaming (_≟_ to _b≟_)
open import MyList

-- free variable
is-fv : ∀ {Γ τ} -> Term Γ τ -> Nat -> Bool
is-fv (var x) n with (index x) ≟ n
is-fv (var x) n | yes p = false -- true
is-fv (var x) n | no ¬p = true --false
is-fv (t₁ $ t₂) n = is-fv t₁ n ∨ is-fv t₂ n
is-fv {Γ} (lam σ t) n with length Γ ≟ n -- = is-fv t n
is-fv (lam σ t) n | yes p = false
is-fv (lam σ t) n | no ¬p = is-fv t n

inc : {Γ : Cxt} -> Nat -> Raw -> Raw
inc zero e = e
inc {Γ} (suc n) e                     with infer Γ e
inc (suc n) .(var (index x))          | ok τ (var x) with is-fv (var x) (index x)
inc (suc n) .(erase (var x))          | ok τ (var x) | true = var (suc (index x))
inc (suc n) .(erase (var x))          | ok τ (var x) | false = var (index x)
inc {Γ} (suc n) .(erase t $ erase t₁) | ok τ (t $ t₁) = inc {Γ} n (erase t) $ inc {Γ} n (erase t₁)
inc {Γ} (suc n) .(lam σ (erase t))    | ok .(σ ⇒ τ) (lam σ {τ} t) = lam σ (inc {σ :: Γ} n (erase t))
inc (suc n) .(eraseBad b) | bad b =  eraseBad b

-- substition E[V := R]
infixl 90 _[_:=_]
_[_:=_] : ∀ {Γ τ} -> Term Γ τ -> Nat -> Raw -> Raw
var v   [ x := s ] with (index v) ≟ x
var v   [ x := s ] | yes _ = s
var v   [ x := s ] | no  _ = var (index v)
(f $ a) [ x := s ] = f [ x := s ] $ a [ x := s ]
{-_[_:=_] {Γ} (lam σ e) x s with (length Γ) ≟ x
lam σ e [ x := s ] | yes _ = lam σ (erase e)
lam σ e [ x := s ] | no  _ = lam σ (e [ suc x := s ]) -- TODO: is-fv
-}
_[_:=_] {Γ} (lam σ e) x s = lam σ (e [ suc x := inc {[]} 1000 s ]) -- TODO: is-fv


β-> : ∀ {Γ τ} -> Term Γ τ -> Raw -- Term Γ τ
β-> (var x) = var (index x)

β-> (var x $ e₂) = (β-> (var x)) $ (β-> e₂)
β-> ((e₁ $ e₂) $ e₃) = β-> (e₁ $ e₂) $ (β-> e₃)
β-> {Γ} (_$_ {σ} (lam .σ e₁) e₂) = e₁ [ 0 := (β-> e₂) ]

{-
β-> (f $ a) with f
β-> (f $ a) | var x = {!!}
β-> (f $ a) | ff $ ff₁ = (β-> ff)
β-> (_$_ {σ} f a) | lam .σ ff = {!!}
-}
β-> (lam σ e) = lam σ (β-> e)

