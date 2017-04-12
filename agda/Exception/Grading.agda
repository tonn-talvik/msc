{-# OPTIONS --type-in-type #-}

module Grading where

open import Relation.Binary.PropositionalEquality
open import Function


record OrderedMonoid : Set where
  infix 90 _·_ -- \cdot
  infix 80 _⊑_ -- \leq \sqsubseteq ⊑ 
  field
    E : Set
    _·_ : E → E → E    
    i : E

    lu : {e : E } → i · e ≡ e
    ru : {e : E } → e ≡ e · i 
    ass : {e e' e'' : E} → (e · e') · e'' ≡ e · (e' · e'')
    
    _⊑_ : E → E → Set    
    ⊑-refl : {e : E} → e ⊑ e
    ⊑-trans : {e e' e'' : E} → e ⊑ e' → e' ⊑ e'' → e ⊑ e''

    mon : {e e' e'' e''' : E} → e ⊑ e'' → e' ⊑ e''' → e · e' ⊑ e'' · e'''



subeq : {E : Set} → {T : E → Set → Set} → {e e' : E} → {X : Set} → e ≡ e' → T e X → T e' X
subeq refl p = p


record GradedMonad : Set where
  field
    OM : OrderedMonoid
    
  open OrderedMonoid OM
  field

    T : E → Set → Set -- TₑX

    η : {X : Set} → X → T i X
    lift : {e e' : E} {X Y : Set} → (X → T e' Y) → (T e X → T (e · e') Y)

    sub : {e e' : E} {X : Set} → e ⊑ e' → T e X → T e' X

    sub-mon : {e e' e'' e''' : E} {X Y : Set} →
              (p : e ⊑ e'') → (q : e' ⊑ e''') → (f : X → T e' Y) → (c : T e X) → 
              sub (mon p q) (lift f c) ≡ lift (sub q ∘ f) (sub p c) 

  sub-eq : {e e' : E} {X : Set} → e ≡ e' → T e X → T e' X
  sub-eq = subeq {E} {T}
 
  field
    sub-refl : {e : E} {X : Set} → (c : T e X) → sub ⊑-refl c ≡ c
    sub-trans : {e e' e'' : E} {X : Set} →
                (p : e ⊑ e') → (q : e' ⊑ e'') → (c : T e X) → 
                sub q (sub p c) ≡ sub (⊑-trans p q) c   

    mlaw1 : {e : E} → {X Y : Set} → (f : X → T e Y) → (x : X) →
            sub-eq lu (lift f (η x)) ≡ f x
    mlaw2 : {e : E} → {X : Set} → (c : T e X) →
            sub-eq ru c ≡ lift η c
    mlaw3 : {e e' e'' : E} → {X Y Z : Set} →
            (f : X → T e' Y) → (g : Y → T e'' Z) → (c : T e X) → 
            sub-eq ass (lift g (lift f c)) ≡ lift (lift g ∘ f) c 

  T₁ : {e : E} {X Y : Set} → (X → Y) → T e X → T e Y
  T₁ f = sub-eq (sym ru) ∘ lift (η ∘ f) 

