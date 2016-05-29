module MyOperationalSemantics where

open import Data.Nat renaming (ℕ to Nat)
open import Data.List renaming (_∷_ to _::_)

open import MyTypes
open import MyExpressions
open import MyTypeInference

----------------------------------------------------------------

open import Relation.Nullary using (yes; no)
open import MyList
open import Data.Integer renaming (_≤?_ to _z≤?_; _≟_ to _z≟_; suc to zsuc; _+_ to _z+_)

add : Nat -> ℤ -> Nat
add n z with + n z+ z
add n z | x with x z≤? - + 1
add n z | x | yes _ = 999999
add n z | x | no  _ = ∣ x ∣

-- d-place shift of a term t above cutoff c is ↑[ d , c ] t 
-- https://github.com/Gabriel439/Haskell-Morte-Library/issues/1
-- based on De Bruijn indices and described in Benjamin Pierce's
-- Types and Programming Languages book on page 79 and 80.
↑[_,_]_ : ℤ -> ℤ -> Raw -> Raw
↑[ d , c ] var x with c z≤? + x
↑[ d , c ] var x | yes _ = var (add x d)
↑[ d , c ] var x | no  _ = var x
↑[ d , c ] t $ u         = (↑[ d , c ] t) $ (↑[ d , c ] u)
↑[ d , c ] lam x t       = lam x (↑[ d , zsuc c ] t)
 
-- substition E[V := R]
infixl 90 _[_:=_]
_[_:=_] : ∀ {Γ τ} -> Term Γ τ -> Nat -> Raw -> Raw
var v   [ x := s ] with (index v) ≟ x
var v   [ x := s ] | yes _ = s
var v   [ x := s ] | no  _ = var (index v)
(t $ u) [ x := s ] = t [ x := s ] $ u [ x := s ]
_[_:=_] {Γ} (lam σ e) x s = lam σ (e [ suc x := (↑[ + 1 , + 0 ] s) ])


β-> : ∀ {Γ τ} -> Term Γ τ -> Raw -- Term Γ τ
β-> (var x) = var (index x)
β-> (var x $ e₂) = (β-> (var x)) $ (β-> e₂)
β-> ((t $ u) $ v) = β-> (t $ u) $ (β-> v)
β-> {Γ} (_$_ {σ} (lam .σ t) u) = ↑[ - + 1 , + 0 ] ( t [ 0 := ↑[ + 1 , + 0 ] (β-> u) ])
β-> (lam σ e) = lam σ (β-> e)

