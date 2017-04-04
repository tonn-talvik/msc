{-# OPTIONS --type-in-type #-}

module OrderedMonoid where

open import Relation.Binary.Core using (_≡_)


record OrderedMonoid : Set where
  infix 90 _·_ -- \cdot
  infix 80 _⊑_ -- \leq \sqsubseteq ⊑ 
  field
    E : Set
    
    _⊑_ : E → E → Set
    
    ⊑-refl : {e : E} → e ⊑ e
    ⊑-trans : {e e' e'' : E} → e ⊑ e' → e' ⊑ e'' → e ⊑ e''

    i : E
    _·_ : E → E → E

    mon : {e e' e'' e''' : E} → e ⊑ e'' → e' ⊑ e''' → e · e' ⊑ e'' · e'''

    lu : {e : E } → i · e ≡ e
    ru : {e : E } → e ≡ e · i 
    ass : {e e' e'' : E} → (e · e') · e'' ≡ e · (e' · e'')




-- https://theorylunch.wordpress.com/2013/12/03/natural-numbers-with-addition-form-a-monoid/
