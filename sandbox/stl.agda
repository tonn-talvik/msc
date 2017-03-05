module stl where

open import Data.Nat renaming (ℕ to Nat)
open import Data.List renaming (_∷_ to _::_)

open import MyTypes
open import MyExpressions
open import MyTypeInference

----------------------------------------------------------------

-- De Bruijn index illustration: λz.(λy.y(λx.x))(λx.zx) is λ(λ1(λ1))(λ2 1)
edebruijn : Raw
edebruijn = 
  lam ((ı ⇒ ı) ⇒ ı)
      ((lam ((ı ⇒ ı) ⇒ ı)
            (var 0 $ (lam ı (var 0))))
       $ (lam (ı ⇒ ı) (var 1 $ var 0)))
tcedebruijn = infer [] edebruijn


ex : Raw
ex = lam ((ı ⇒ ı) ⇒ ı) (var 0 $ (lam ı (var 0)))

e0 e1 e2 e3 : Raw
e0 = lam (ı ⇒ ı) (lam ı (var 0))
e1 = lam (ı ⇒ ı) (lam ı (var 1 $ var 0))
e2 = lam (ı ⇒ ı) (lam ı (var 1 $ (var 1 $ var 0)))
e3 = lam (ı ⇒ ı) (lam ı (var 1 $ (var 1 $ (var 1 $ var 0))))

esucc : Raw -- λn.λf.λx.f (n f x)
esucc = lam ((ı ⇒ ı) ⇒ ı ⇒ ı) 
            (lam (ı ⇒ ı) 
                 (lam ı 
                      (var 1 $ (var 2 $ var 1 $ var 0))))

-- eplus : Raw -- λm.λn.λf.λx.m f (n f x)
-- etrue : Raw -- λx.λy.x
-- efalse : Raw -- λx.λy.y
-- eand := λp.λq.p q 
-- eor := λp.λq.p p q
-- enot := λp.λa.λb.p b a
-- eifthenelse := λp.λa.λb.p a b 
--Γ = ı :: []
tc = infer [] e1 -- Γ e

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Bool renaming (_≟_ to _b≟_)
open import MyList
is-fv : ∀ {Γ τ} -> Term Γ τ -> Nat -> Bool
is-fv (var x) n with (index x) ≟ n
is-fv (var x) n | yes p = true
is-fv (var x) n | no ¬p = false
is-fv (t₁ $ t₂) n = is-fv t₁ n ∨ is-fv t₂ n
is-fv {Γ} (lam σ t) n with length Γ ≟ n -- = is-fv t n
is-fv (lam σ t) n | yes p = false
is-fv (lam σ t) n | no ¬p = is-fv t n

-- very Γ sensitive...
t-fv : Raw -> Nat -> Bool
t-fv e n with infer [] e
t-fv .(erase t) n | ok τ t = is-fv t n
t-fv .(eraseBad b) n | bad b = false


-- substition E[V := R]
infixl 90 _[_:=_]
_[_:=_] : ∀ {Γ τ} -> Term Γ τ -> Nat -> Raw -> Raw
var v   [ x := s ] with (index v) ≟ x
var v   [ x := s ] | yes _ = s
var v   [ x := s ] | no  _ = var (index v)
(f $ a) [ x := s ] = f [ x := s ] $ a [ x := s ]
_[_:=_] {Γ} (lam σ e) x s with (length Γ) ≟ x
lam σ e [ x := s ] | yes p = lam σ (erase e)
lam σ e [ x := s ] | no ¬p = lam σ (e [ suc x := s ]) -- TODO: is-fv


β-> : ∀ {Γ τ} -> Term Γ τ -> Raw -- Term Γ τ
β-> (var x) = var (index x)
--β-> {Γ} (e₁ $ e₂) = e₁ [ 0 := erase e₂ ] -- ????
β-> (var x $ e₂) = (β-> (var x)) $ (β-> e₂)
β-> ((e₁ $ e₂) $ e₃) = β-> (e₁ $ e₂) $ β-> e₃
β-> (_$_ {σ} (lam .σ e₁) e₂) = e₁ [ 0 := (β-> e₂) ]
β-> (lam σ e) = lam σ (β-> e)


beta-tester : Raw -> Raw
beta-tester e with infer (ı :: ı :: []) e
beta-tester .(erase t) | ok τ t = β-> t
beta-tester .(eraseBad b) | bad b = eraseBad b

beta-test1 = beta-tester (lam ı (var 0) $ (var 1))
beta-test = beta-tester (esucc $ e0)
beta-test2 = beta-tester beta-test
beta-test3 = beta-tester beta-test2
