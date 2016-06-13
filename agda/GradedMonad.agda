{-# OPTIONS --type-in-type #-}

module GradedMonad where

open import OrderedMonoid

record GradedMonad : Set where
  field
    OM : OrderedMonoid
    
  open OrderedMonoid.OrderedMonoid OM
  field

    T : M → Set → Set -- TₑX

    η : {X : Set} → X → T i X
    lift : {e e' : M} {X Y : Set} → (X → T e' Y) → (T e X → T (e · e') Y)




