{-# OPTIONS --type-in-type #-}

module OrderedMonoid where

open import Relation.Binary.Core using (_≡_ ; refl)

record OrderedMonoid : Set where
  field
    M : Set
    
    _⊑_ : M → M → Set -- \leq \sqsubseteq ⊑ 
    
    reflM : {m : M} → m ⊑ m
    transM : {m n o : M} → m ⊑ n → n ⊑ o → m ⊑ o

    i : M 
    _·_ : M → M → M -- \cdot

    mon : {m n m' n' : M} → m ⊑ m' → n ⊑ n' → (m · n) ⊑ (m' · n')

    lu : { m : M } → (i · m) ≡ m
    ru : { m : M } → m ≡ m · i 
    ass : { m n o : M} → (m · n) · o ≡ m · (n · o)




-- https://theorylunch.wordpress.com/2013/12/03/natural-numbers-with-addition-form-a-monoid/
