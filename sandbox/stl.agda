module stl where

open import Data.Nat renaming (ℕ to Nat)
open import Data.List renaming (_∷_ to _::_)
open import Data.Bool renaming (_≟_ to _b≟_)

open import MyTypes
open import MyExpressions
open import MyTypeInference
open import MyOperationalSemantics

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

exx : Raw
exx = lam ı (lam ı (var 1)) $ (var 0)

-- Church numerals illustration
e0 e1 e2 e3 : Raw
e0 = lam (ı ⇒ ı) (lam ı (var 0))
e1 = lam (ı ⇒ ı) (lam ı (var 1 $ var 0))
e2 = lam (ı ⇒ ı) (lam ı (var 1 $ (var 1 $ var 0)))
e3 = lam (ı ⇒ ı) (lam ı (var 1 $ (var 1 $ (var 1 $ var 0))))

esucc : Raw -- λn.λf.λx.f (n f x)
esucc = lam ((ı ⇒ ı) ⇒ ( ı ⇒ ı)) -- 2 n
            (lam (ı ⇒ ı)           -- 1 f
                 (lam ı             -- 0 x
                      (var 1 $ (var 2 $ var 1 $ var 0))))


eplus : Raw -- λm.λn.λf.λx.m f (n f x)
eplus = lam ((ı ⇒ ı) ⇒ ( ı ⇒ ı))      -- 3 m
            (lam ((ı ⇒ ı) ⇒ ( ı ⇒ ı)) -- 2 n
                 (lam (ı ⇒ ı)           -- 1 f
                      (lam ı             -- 0 x
                           (var 3 $ var 1 $ (var 2 $ var 1 $ var 0)))))


-- etrue : Raw -- λx.λy.x
-- efalse : Raw -- λx.λy.y
-- eand := λp.λq.p q 
-- eor := λp.λq.p p q
-- enot := λp.λa.λb.p b a
-- eifthenelse := λp.λa.λb.p a b 

-- very Γ sensitive...
t-fv : Raw -> Nat -> Bool
t-fv e n with infer [] e
t-fv .(erase t) n | ok τ t = is-fv t n
t-fv .(eraseBad b) n | bad b = false

beta-tester : Cxt -> Raw -> Raw
beta-tester Γ e with infer Γ e
beta-tester Γ .(erase t) | ok τ t = β-> t
beta-tester Γ .(eraseBad b) | bad b = var 666 -- eraseBad b

beta-test : Cxt -> Raw -> Nat -> Raw
beta-test Γ e zero = e
beta-test Γ e (suc n) = beta-test Γ (beta-tester Γ e) n

tc-succ-0 = beta-test [] (esucc $ e0)
tc-succ-1 = beta-test [] (esucc $ e1)
tc-succ-2 = beta-test [] (esucc $ e2)
tc-succ-3 = beta-test [] (esucc $ e3)

tc-plus-3-1 = beta-test [] (eplus $ e3 $ e1)

ey : Raw
ey = (lam (ı ⇒ ı) (lam ı (var 1 $ var 0))) $ var 1
gy = (ı :: ı ⇒ ı :: [])
ty = beta-test gy ey -- we should get: lam i (var 2 $ var 0)

ez : Raw
ez = (lam ı (var 2 $ var 0)) $ var 0
gz = ı :: ı ⇒ ı :: []
tz = beta-test gz ez

-- is-fv is always false for well-typed terms?
--tz = inc {ı :: ı :: []} 10 (var 1)
--tz = inc 0 (var 1)

 
