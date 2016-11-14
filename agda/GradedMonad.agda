{-# OPTIONS --type-in-type #-}

module GradedMonad where

open import Relation.Binary.PropositionalEquality
open import Function

open import OrderedMonoid

subeq : {M : Set} → {T : M → Set → Set} → {e e' : M} → {X : Set} → e ≡ e' → T e X → T e' X
subeq refl p = p


record GradedMonad : Set where
  field
    OM : OrderedMonoid
    
  open OrderedMonoid.OrderedMonoid OM
  field

    T : M → Set → Set -- TₑX

    η : {X : Set} → X → T i X
    lift : {e e' : M} {X Y : Set} → (X → T e' Y) → (T e X → T (e · e') Y)

    sub : {e e' : M} {X : Set} → e ⊑ e' → T e X → T e' X

    sub-mon : {e e' e'' e''' : M} {X Y : Set} →
              (p : e ⊑ e'') → (q : e' ⊑ e''') → (f : X → T e' Y) → (c : T e X) → 
              sub (mon p q) (lift f c) ≡ lift (sub q ∘ f) (sub p c) 

  sub-eq : {e e' : M} {X : Set} → e ≡ e' → T e X → T e' X

  sub-eq = subeq {M} {T}
 
  field
    sub-refl : {e : M} {X : Set} → (c : T e X) → sub reflM c ≡ c
    sub-trans : {e e' e'' : M} {X : Set} →
                (p : e ⊑ e') → (q : e' ⊑ e'') → (c : T e X) → 
                sub q (sub p c) ≡ sub (transM p q) c   

    mlaw1 : {e : M} → {X Y : Set} → (f : X → T e Y) → (x : X) →
            sub-eq lu (lift f (η x)) ≡ f x
    mlaw2 : {e : M} → {X : Set} → (c : T e X) →
            sub-eq ru c ≡ lift η c
    mlaw3 : {e e' e'' : M} → {X Y Z : Set} →
            (f : X → T e' Y) → (g : Y → T e'' Z) → (c : T e X) → 
            sub-eq ass (lift g (lift f c)) ≡ lift (lift g ∘ f) c 
