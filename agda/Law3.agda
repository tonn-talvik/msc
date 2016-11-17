module Law3 where

open import Data.Nat
open import Data.List

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


_≡++_ : {X : Set} → {xs xs' ys ys' : List X} → xs ≡ xs' → ys ≡ ys' → xs ++ ys ≡ xs' ++ ys'
-- _≡++_ = cong₂ _++_
refl ≡++ refl = refl


liftND : {X Y : Set} → (X → List Y) → (List X → List Y)
liftND f [] = []
liftND f (x ∷ xs) = f x ++ liftND f xs

lemma++ : {X : Set} (xs xs' xs'' : List X) →
          xs ++ (xs' ++ xs'') ≡ (xs ++ xs') ++ xs''
lemma++ [] xs' xs'' = begin 
                         xs' ++ xs'' 
                      ∎ --refl
lemma++ (x ∷ xs) xs' xs'' = 
                      begin
                        (x ∷ xs) ++ (xs' ++ xs'')
                      ≡⟨ refl ⟩
                         x ∷ (xs ++ (xs' ++ xs''))
                      ≡⟨ cong (_∷_ x) (lemma++ xs xs' xs'') ⟩
                         x ∷ ((xs ++ xs') ++ xs'')
                      ≡⟨ refl ⟩
                         (x ∷ (xs ++ xs')) ++ xs''
                      ≡⟨ refl ⟩
                         ((x ∷ xs) ++ xs') ++ xs'' 
                      ∎
                        --cong (_∷_ x) (lemma++ xs xs' xs'')


-- rewrite lemma++ xs xs' xs'' = refl

lemma : {X Y : Set} → (f : X → List Y) → (xs xs' : List X) → 
    liftND f (xs ++ xs') ≡ liftND f xs ++ liftND f xs'
lemma f [] xs' = refl
lemma f (x ∷ xs) xs' rewrite lemma f xs xs' = lemma++ (f x) (liftND f xs) (liftND f xs')



mlaw3ND : {X Y Z : Set} → 
          (f : X → List Y) → (g : Y → List Z) → (c : List X) → 
                   (liftND g (liftND f c))
          ≡ liftND (λ x → liftND g (f x)) c
mlaw3ND f g [] = refl
mlaw3ND f g (x ∷ xs) = begin 
                          liftND g (liftND f (x ∷ xs))
                        ≡⟨ refl ⟩
                          liftND g (f x ++ liftND f xs)
                        ≡⟨ lemma g (f x) (liftND f xs) ⟩
                          liftND g (f x) ++ liftND g (liftND f xs)
                        ≡⟨ refl {x = liftND g (f x)} ≡++ mlaw3ND f g xs ⟩
                          liftND g (f x) ++ liftND (λ x → liftND g (f x)) xs
                        ≡⟨ refl ⟩
                          liftND (λ x → liftND g (f x)) (x ∷ xs)
                        ∎ 


-- trans (lemma g (f x) (liftND f xs)) (cong (_++_ (liftND g (f x))) (mlaw3ND f g xs))


data BVec (X : Set) : ℕ → Set where
  [] : {n : ℕ} → BVec X n 
  _∷_ : {n : ℕ} → X → BVec X n → BVec X (suc n)

inflate : {X : Set} → {m n : ℕ} → BVec X n → BVec X (m + n)
inflate = {!!} 

_++B_ : {X : Set} → {m n : ℕ} → BVec X m → BVec X n → BVec X (m + n)
_++B_ {m} {n} [] xs' = inflate {m} {n} xs' 
(x ∷ xs) ++B xs' = x ∷ (xs ++B xs') 
