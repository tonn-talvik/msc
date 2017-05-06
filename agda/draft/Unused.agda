module Unused where

open import Data.Nat
open import Data.Vec

open import Relation.Binary.PropositionalEquality hiding ([_]; inspect)

open ≡-Reasoning


ru+ : {n : ℕ} → n ≡ n + 0
ru+ {zero} = refl
ru+ {suc n} = cong suc (ru+ {n}) 


ass+ : {m n o : ℕ} → (m + n) + o ≡ m + (n + o)
ass+ {zero} = refl
ass+ {suc m} = cong suc (ass+ {m})


zl* : {m : ℕ} → m * 0 ≡ 0
zl* {zero} = refl
zl* {suc m} = zl* {m}
zr* : {m : ℕ} → 0 ≡ m * 0
zr* {zero} = refl
zr* {suc m} = zr* {m}

lem1 : {m n : ℕ} → m + suc n ≡ suc m + n
lem1 {zero} = refl
lem1 {suc m} {n} = cong suc (lem1 {m})

comm+ : {m n : ℕ} → m + n ≡ n + m
comm+ {zero} = {!!} --ru+
comm+ {suc m} {zero} = cong suc (comm+ {m})
comm+ {suc m} {suc n} = cong suc (
  begin
    m + suc n
  ≡⟨ lem1 {m} {n} ⟩
    suc m + n
  ≡⟨ comm+ {suc m} ⟩
    n + suc m 
  ∎)

-- FIXME :-)
comm* : {m n : ℕ} → m * n ≡ n * m
comm* {zero} {n} = zr* {n}
comm* {suc m} {zero} = comm* {m}
comm* {suc m} {suc n} = cong suc (
  begin
    n + m * suc n
  ≡⟨ cong (_+_ n) (comm* {m}) ⟩
    n + suc n * m
  ≡⟨ cong (_+_ n) (comm+ {m}) ⟩
    n + (n * m + m)
  ≡⟨ cong (_+_ n) (cong (λ x → x + m) (comm* {n})) ⟩
    n + (m * n + m)
  ≡⟨ sym (ass+ {n}) ⟩
    (n + m * n) + m
  ≡⟨ comm+ {n + m * n} ⟩
    m + suc m * n
  ≡⟨ cong (_+_ m) (comm* {suc m} {n}) ⟩
    m + n * suc m
  ∎)



lemma-cong0+ : {e e' : ℕ} {p : e ≡ e'} → 
               cong (_+_ 0) p ≡ p
lemma-cong0+ {p = refl} = refl

lemma-trans : {E : Set} {e e' : E} {p : e ≡ e'} →
              trans p refl ≡ p
lemma-trans {p = refl} = refl

lemma-sym-cong : {X : Set} {x x' : X} {f : X → X} {p : x ≡ x'} →
                 sym (cong f p) ≡ cong f (sym p)
lemma-sym-cong {p = refl} = refl

lemma-trans-cong : {X : Set} {x x' x'' : X}
                   {f : X → X} {p : x ≡ x'} {q : x' ≡ x''} →
                   trans (cong f p) (cong f q) ≡ cong f (trans p q)
lemma-trans-cong {p = refl} = refl

lemma-suc : {m n n' : ℕ} {p : n ≡ n'} →
            cong (_+_ (suc m)) p ≡ cong suc (cong (_+_ m) p)
lemma-suc {p = refl} = refl

{-
lemma-head : {X : Set} {x : X} {e e' e'' : ℕ}
             {xs : Vec X e} {xs' : Vec X e'}
             {p : e ≡ e''} {q : e' ≡ e''}
             {tail : subV p xs ≡ subV q xs'} →
             subV (cong suc p) (x ∷ xs)
             ≡ subV (cong suc q) (x ∷ xs')
lemma-head {p = refl} {q = refl} {tail = refl} = refl
 -}
