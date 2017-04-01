module Optimization where

open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open import Exception
open import OrderedMonoid
open import GradedMonad
open GradedMonad.GradedMonad ExcEffGM
open OrderedMonoid.OrderedMonoid ExcEffOM

{-

need to compare:

lift {errok} {errok · e'}  (λ x → lift {errok} {e'} (λ y → ⟦ n ⟧c (y , x , ρ)) (⟦ m ⟧c ρ)) ((⟦ m ⟧c ρ)

lift {errok} {e'} (λ x → ⟦ n ⟧c (x , x , ρ)) (⟦ m ⟧c ρ)


-}

errok-seq : (e : Exc) → errok · (errok · e) ≡ errok · e
errok-seq e = sym (ass {errok} {errok} {e})


dup-comp : {e : Exc}{X Y : Set}  → (m : T errok X) → (n : X → X → T e Y) → 
           sub-eq (errok-seq e) (lift {errok} {errok · e}
                                      (λ x → lift {errok} {e} (λ y → n y x) m)
                                      m)
           ≡ lift {errok} {e} (λ x → n x x) m
dup-comp {err} m n = refl
dup-comp {ok} (just x) n =  refl
dup-comp {ok} nothing n = refl
dup-comp {errok} (just x) n = refl
dup-comp {errok} nothing n = refl 


dead-comp : {e : Exc} {X Y : Set} → (m : T ok X) → (n : T e Y) →
            lift {ok} {e} (λ _ → n) m ≡ n
dead-comp m n  = refl
