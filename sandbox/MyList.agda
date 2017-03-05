module MyList where

open import Data.Nat
open import Data.List renaming (_∷_ to _::_)

data _∈_ {A : Set}(x : A) : List A -> Set where
  hd : forall {xs} -> x ∈ (x :: xs)
  tl : forall {y xs} -> x ∈ xs -> x ∈ (y :: xs)

index : forall {A}{x : A}{xs} -> x ∈ xs -> ℕ
index hd = zero
index (tl p) = suc (index p)

data Lookup {A : Set}(xs : List A) : ℕ -> Set where
  inside : (x : A)(p : x ∈ xs) -> Lookup xs (index p)
  outside : (m : ℕ) -> Lookup xs (length xs + m)

_!_ : {A : Set}(xs : List A)(n : ℕ) -> Lookup xs n
[] ! n = outside n
(x :: xs) ! zero = inside x hd
(x :: xs) ! suc n with xs ! n
(x :: xs) ! suc .(index p) | inside y p = inside y (tl p)
(x :: xs) ! suc .(length xs + n) | outside n = outside n
