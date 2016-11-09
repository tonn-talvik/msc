module Law3 where

open import Data.Nat
open import Data.List

open import Relation.Binary.PropositionalEquality

liftND : {X Y : Set} → (X → List Y) → (List X → List Y)
liftND f [] = []
liftND f (x ∷ xs) = f x ++ liftND f xs

lemma++ : {X : Set} (xs xs' xs'' : List X) →
          xs ++ (xs' ++ xs'') ≡ (xs ++ xs') ++ xs''
lemma++ [] xs' xs'' = refl
lemma++ (x ∷ xs) xs' xs'' rewrite lemma++ xs xs' xs'' = refl

lemma : {X Y : Set} → (f : X → List Y) → (xs xs' : List X) → 
    liftND f (xs ++ xs') ≡ liftND f xs ++ liftND f xs'
lemma f [] xs' = refl
lemma f (x ∷ xs) xs' rewrite lemma f xs xs' = lemma++ (f x) (liftND f xs) (liftND f xs')


mlaw3ND : {X Y Z : Set} → 
          (f : X → List Y) → (g : Y → List Z) → (c : List X) → 
                   (liftND g (liftND f c))
          ≡ liftND (λ x → liftND g (f x)) c
mlaw3ND f g [] = refl
mlaw3ND f g (x ∷ xs) = trans (lemma g (f x) (liftND f xs)) (cong (_++_ (liftND g (f x))) (mlaw3ND f g xs))


data BVec (X : Set) : ℕ → Set where
  [] : {n : ℕ} → BVec X n 
  _∷_ : {n : ℕ} → X → BVec X n → BVec X (suc n)

inflate : {X : Set} → {m n : ℕ} → BVec X n → BVec X (m + n)
inflate = {!!} 

_++B_ : {X : Set} → {m n : ℕ} → BVec X m → BVec X n → BVec X (m + n)
_++B_ {m} {n} [] xs' = inflate {m} {n} xs' 
(x ∷ xs) ++B xs' = x ∷ (xs ++B xs') 
