{-# OPTIONS --type-in-type #-}

module ESemantics where

open import Data.Unit hiding (_≟_; _≤_)
open import Data.Product

open import Data.Maybe
open import Data.Fin hiding (lift)
open import Data.Nat hiding (_≟_; _⊔_; _≤_)
open import Data.Bool hiding (T ; _≟_; _∨_)
open import Data.List
open import Relation.Binary.Core using (_≡_ ; refl)
open import Relation.Binary.PropositionalEquality

open import Finiteness
open import ELanguage
open import GradedMonad
open import OrderedMonoid
open import Exception
open OrderedMonoid.OrderedMonoid ExcEffOM
open GradedMonad.GradedMonad ExcEffGM


sfail : {X : Set} → T err X
sfail = tt

{-
sor : {e e' : E} {X : Set} → T e X → T e' X → T (e ⊔ e') X 
sor {err} {err} _ _ = tt
sor {err} {ok} _ x' = just x'
sor {err} {errok} _ x' = x'
sor {ok} {err} x _ = just x
sor {ok} {ok} x _ = x
sor {ok} {errok} x _ = just x
sor {errok} (just x) x' = just x
sor {errok} {err} nothing x' = nothing
sor {errok} {ok} nothing x' = just x'
sor {errok} {errok} nothing x' = x'
-}

sor : (e e' : E) {X : Set} → T e X → T e' X → T (e ⊹ e') X
sor err _ _ x' = x'
sor ok _ x _ = x
sor errok err x _ = x
sor errok ok (just x) _ = x
sor errok ok nothing x' = x'
sor errok errok (just x) x' = just x
sor errok errok nothing x' = x'


----------------------------------------------------------------------

mutual
  ⟪_⟫v : VType → Set
  ⟪ nat ⟫v = ℕ
  ⟪ bool ⟫v = Bool
  ⟪ t ∏ u ⟫v = ⟪ t ⟫v × ⟪ u ⟫v
  ⟪ t ⟹ c ⟫v = ⟪ t ⟫v → ⟪ c ⟫c

  ⟪_⟫c : CType → Set
  ⟪ ε / t ⟫c = T ε ⟪ t ⟫v

⟦_⟧x : Ctx → Set
⟦ [] ⟧x = ⊤
⟦ σ ∷ Γ ⟧x = ⟪ σ ⟫v × ⟦ Γ ⟧x


proj : {Γ : Ctx} {σ : VType} → σ ∈ Γ → ⟦ Γ ⟧x → ⟪ σ ⟫v
proj (here' refl) ρ = proj₁ ρ
proj (there x) ρ = proj x (proj₂ ρ)


primrecT : {e e' : E} {t : Set} → ℕ → T e' t → (ℕ → t → T e t) → e' · e ⊑ e' → T e' t
primrecT zero z s p = z
primrecT {e} {e'} (suc n) z s p = sub p (lift {e'} {e} (s n) (primrecT n z s p)) 


mutual
  vcast : {σ σ' : VType} →  σ ≤V σ' → ⟪ σ ⟫v → ⟪ σ' ⟫v
  vcast st-refl x = x
  vcast st-bn x = 0
  --vcast (st-trans o o') x = vcast o' (vcast o x)
  vcast (st-prod o o') (proj , proj') = vcast o proj , vcast o' proj'
  vcast (st-func e o) f = λ x → ccast o (f (vcast e x))

  ccast : {τ τ' : CType} → τ ≤C τ' → ⟪ τ ⟫c → ⟪ τ' ⟫c
  ccast (st-comp {ε} {ε'} e o) c = T₁ {ε'} (vcast o) (sub e c)

mutual
  ⟦_⟧v : {Γ : Ctx} {σ : VType} → VTerm' Γ ( σ) → ⟦ Γ ⟧x → ⟪ σ ⟫v
  ⟦ TT ⟧v ρ = true
  ⟦ FF ⟧v ρ = false
  ⟦ ZZ ⟧v ρ = zero
  ⟦ SS t ⟧v ρ = suc (⟦ t ⟧v ρ)
  ⟦ ⟨ t , t' ⟩ ⟧v ρ = ⟦ t ⟧v ρ , ⟦ t' ⟧v ρ
  ⟦ FST t ⟧v ρ = proj₁ (⟦ t ⟧v ρ)
  ⟦ SND t ⟧v ρ = proj₂ (⟦ t ⟧v ρ)
  ⟦ VAR x ⟧v ρ = proj x ρ
--  ⟦ LAM σ {_ / _} t ⟧v ρ = λ x → ⟦ t ⟧c (x , ρ)
  ⟦ LAM σ t ⟧v ρ = λ x → ⟦ t ⟧c (x , ρ)
  ⟦ VCAST t p ⟧v ρ = vcast p (⟦ t ⟧v ρ)
  
  --⟦_⟧c : {Γ : Ctx} {e : E} {σ : VType} → CTerm Γ (e / σ) → ⟦ Γ ⟧x → T e ⟪ σ ⟫v
  ⟦_⟧c : {Γ : Ctx} {τ : CType} → CTerm' Γ τ → ⟦ Γ ⟧x → ⟪ τ ⟫c
  ⟦ VAL v ⟧c ρ = η (⟦ v ⟧v ρ)
  ⟦ FAIL σ ⟧c ρ = sfail {⟪ σ ⟫v}
  ⟦ TRY_WITH_ {e} {e'} t u ⟧c ρ = sor e e' (⟦ t ⟧c ρ) (⟦ u ⟧c ρ)
  ⟦ IF_THEN_ELSE_ {e} {e'} b m n ⟧c ρ = if ⟦ b ⟧v ρ
                                       then (sub (lub e e') (⟦ m ⟧c ρ))
                                       else (sub (lub-sym e' e) (⟦ n ⟧c ρ))
  --⟦ PREC v m n p ⟧c ρ = primrecT (⟦ v ⟧v ρ) (⟦ m ⟧c ρ) (λ i → λ acc → ⟦ n ⟧c (acc , i , ρ)) p
  ⟦ t $ u ⟧c ρ = ⟦ t ⟧v ρ (⟦ u ⟧v ρ)
  ⟦ LET_IN_ {e} {e'} m n ⟧c ρ = lift {e} {e'} (λ x → ⟦ n ⟧c (x , ρ)) (⟦ m ⟧c ρ)
  ⟦ CCAST t o ⟧c ρ = ccast o (⟦ t ⟧c ρ)


--xxx = ⟦_⟧c ((VAR here) $ ZZ ) (suc , tt)


dropt : {Γ : Ctx} → ⟦ Γ ⟧x  → {σ : VType}  → (x : σ ∈ Γ) → 
     ⟦ dropT Γ x  ⟧x 
dropt (_ , ρ) (here' refl) = ρ
dropt (v , ρ) (there x) = v , dropt ρ x

lemmaVar : {Γ : Ctx} → (ρ : ⟦ Γ ⟧x) → {σ : VType} 
  → (x : σ ∈ Γ) 
  → {τ : VType} → (y : τ ∈ dropT Γ x) → proj (wkvar x y) ρ ≡ proj y (dropt ρ x)
lemmaVar ρ (here' refl) y = refl
lemmaVar ρ (there x) (here' refl) = refl
lemmaVar {_ ∷ Γ} (_ , ρ) (there x) (there y) = lemmaVar ρ x y


mutual 
 lemmaV : {Γ : Ctx} → (ρ : ⟦ Γ ⟧x) → {σ : VType} 
  → (x : σ ∈ Γ) 
  → {τ : VType} → (t : VTerm' (dropT Γ x) τ) → ⟦ wkV x t ⟧v ρ ≡ ⟦ t ⟧v (dropt ρ x)
 lemmaV ρ x TT = refl
 lemmaV ρ x FF = refl
 lemmaV ρ x ZZ = refl
 lemmaV ρ x (SS t) = cong suc (lemmaV ρ x t)
 lemmaV ρ x ⟨ t , u ⟩ = {!!}
 lemmaV ρ x (FST t) =  cong proj₁ (lemmaV ρ x t)
 lemmaV ρ x (SND t) = cong proj₂ (lemmaV ρ x t)
 lemmaV ρ x (VAR y) = lemmaVar ρ x y
 lemmaV ρ x (LAM σ t) =  funext (λ z → ⟦ wkC (there x) t ⟧c (z , ρ)) (λ z → ⟦ t ⟧c (z , dropt ρ x))  (λ z → lemmaC (z , ρ) (there x) t) 
 lemmaV ρ x (VCAST t p) = {!!}
  
 lemmaC : {Γ : Ctx} → (ρ : ⟦ Γ ⟧x) → {σ : VType} 
  → (x : σ ∈ Γ) 
  → {τ : CType} → (t : CTerm' (dropT Γ x) τ) → ⟦ wkC x t ⟧c ρ ≡ ⟦ t ⟧c (dropt ρ x)
 lemmaC ρ  x t = {!!}


dead-comp' : {Γ : Ctx} {σ τ : VType} {ε : Exc}
             (m : CTerm' Γ (ok / σ)) (n : CTerm' Γ (ε / τ ) ) →
             -- show that n does not depend on m
             (ρ : ⟦ Γ ⟧x) → 
             ⟦ LET m IN (wkC here n) ⟧c ρ ≡ ⟦ n ⟧c ρ --λ ρ → ⟦ n ⟧c (⟦ m ⟧c ρ , ρ)
dead-comp' m n ρ = lemmaC ((⟦ m ⟧c ρ , ρ)) here n  



⟪_⟫x = ⟦_⟧x

----------------------------------------------------------------------

ctrT : {Γ : Ctx} {σ : VType} → σ ∈ Γ → Ctx
ctrT {σ ∷ Γ} (here' refl) = σ ∷ σ ∷ Γ
ctrT {σ ∷ Γ} (there p) = σ ∷ ctrT p

ctrvar : {Γ : Ctx} {σ τ : VType} →
        (p : σ ∈ Γ) → τ ∈ ctrT p → τ ∈ Γ
ctrvar (here' refl) (here' refl) = here' refl
ctrvar (here' refl) (there q) = q
ctrvar (there p) (here' refl) = here' refl
ctrvar (there p) (there q) = there (ctrvar p q)

mutual
  ctrV : {Γ : Ctx} {σ : VType} {τ : VType} →
        (p : σ ∈ Γ) → VTerm' (ctrT p) τ → VTerm' Γ τ
  ctrV p TT = TT
  ctrV p FF = FF
  ctrV p ZZ = ZZ
  ctrV p (SS t) = SS (ctrV p t)
  ctrV p ⟨ t , t' ⟩ = ⟨ ctrV p t , ctrV p t' ⟩
  ctrV p (FST t) = FST (ctrV p t)
  ctrV p (SND t) = SND (ctrV p t)
  ctrV p (VAR x) = VAR (ctrvar p x)
  ctrV p (LAM σ t) = LAM σ (ctrC (there p) t)
  ctrV p (VCAST t q) = VCAST (ctrV p t) q
  
  ctrC : {Γ : Ctx} {σ : VType} {τ : CType} →
        (p : σ ∈ Γ) → CTerm' (ctrT p) τ → CTerm' Γ τ
  ctrC p (VAL x) = VAL (ctrV p x)
  ctrC p (FAIL σ) = FAIL σ
  ctrC p (TRY t WITH t') = TRY ctrC p t WITH ctrC p t'
  ctrC p (IF x THEN t ELSE t') = IF ctrV p x THEN ctrC p t ELSE ctrC p t'
  ctrC p (f $ x) = ctrV p f $ ctrV p x
  ctrC {Γ} p (LET t IN t') = LET ctrC p t IN ctrC (there p) t'
  ctrC p (CCAST t q) = CCAST (ctrC p t) q


ctr : {Γ : Ctx} → ⟪ Γ ⟫x →
      {σ : VType} → 
      (p : σ ∈ Γ) → ⟪ ctrT p ⟫x
ctr (w , ρ) (here' refl) = w , w , ρ
ctr (w , ρ) (there p) = w , ctr ρ p


lemma-ctr-var : {Γ : Ctx} (ρ : ⟪ Γ ⟫x) →
                {σ : VType} (p : σ ∈ Γ) →
                {τ : VType} (x : τ ∈ ctrT p) →
                proj x (ctr ρ p) ≡ proj (ctrvar p x) ρ
lemma-ctr-var ρ (here' refl) (here' refl) = refl
lemma-ctr-var ρ (here' refl) (there x) = refl
lemma-ctr-var ρ (there p) (here' refl) = refl
lemma-ctr-var (w , ρ) (there p) (there x) = lemma-ctr-var ρ p x

mutual
  lemma-ctrV : {Γ : Ctx} (ρ : ⟪ Γ ⟫x) →
               {σ : VType} (p : σ ∈ Γ) →
               {τ : VType} (t : VTerm' (ctrT p) τ) →
               ⟦ t ⟧v (ctr ρ p) ≡ ⟦ ctrV p t ⟧v ρ
  lemma-ctrV ρ p TT = refl
  lemma-ctrV ρ p FF = refl
  lemma-ctrV ρ p ZZ = refl
  lemma-ctrV ρ p (SS t) = cong suc (lemma-ctrV ρ p t)
  lemma-ctrV ρ p ⟨ t , t' ⟩ = cong₂ _,_ (lemma-ctrV ρ p t) (lemma-ctrV ρ p t')
  lemma-ctrV ρ p (FST t) = cong proj₁ (lemma-ctrV ρ p t)
  lemma-ctrV ρ p (SND t) = cong proj₂ (lemma-ctrV ρ p t)
  lemma-ctrV ρ p (VAR x) = lemma-ctr-var ρ p x
  lemma-ctrV ρ p (LAM σ x) = funext (λ z → ⟦ x ⟧c (z , ctr ρ p))
                                      (λ z → ⟦ ctrC (there p) x ⟧c (z , ρ))
                                      (λ z → lemma-ctrC (z , ρ) (there p) x)
  lemma-ctrV ρ p (VCAST t q) = cong (vcast q) (lemma-ctrV ρ p t)
  
  lemma-ctrC : {Γ : Ctx} (ρ : ⟪ Γ ⟫x) →
               {σ : VType} (p : σ ∈ Γ) →
               {τ : CType} (t : CTerm' (ctrT p) τ) →
               ⟦ t ⟧c (ctr ρ p) ≡ ⟦ ctrC p t ⟧c ρ
  lemma-ctrC ρ p (VAL x) = cong η (lemma-ctrV ρ p x)
  lemma-ctrC ρ p (FAIL σ) = refl
  lemma-ctrC ρ p (TRY_WITH_ {e} {e'} t t') = cong₂ (sor e e') (lemma-ctrC ρ p t) (lemma-ctrC ρ p t')
  lemma-ctrC ρ p (IF x THEN t ELSE t') rewrite lemma-ctrV ρ p x | lemma-ctrC ρ p t | lemma-ctrC ρ p t' = refl
  lemma-ctrC ρ p (f $ x) rewrite lemma-ctrV ρ p f | lemma-ctrV ρ p x = {!!} -- refl
  lemma-ctrC ρ p (LET_IN_ {e} {e'} t t') rewrite lemma-ctrC ρ p t =
    cong (λ f → lift {e} {e'} f (⟦ ctrC p t ⟧c ρ))
         (funext (λ w → ⟦ t' ⟧c (w , ctr ρ p))
                 (λ w → ⟦ ctrC (there p) t' ⟧c (w , ρ))
                 (λ w → lemma-ctrC (w , ρ) (there p) t'))
  lemma-ctrC ρ p (CCAST t q) = cong (ccast q) (lemma-ctrC ρ p t)
 


errok-seq : (e : Exc) → errok · (errok · e) ≡ errok · e
errok-seq e = sym (ass {errok} {errok} {e})


dup-comp' : {e : Exc} {Γ : Ctx} {X Y : VType} 
            (m : CTerm' Γ (errok / X)) (n : CTerm' (ctrT here) (e / Y)) →
            (ρ : ⟪ Γ ⟫x) → 
            sub-eq (errok-seq e)
                   (⟦ LET m IN LET wkC here m IN n ⟧c ρ)
            ≡ ⟦ LET m IN ctrC here n ⟧c ρ

dup-comp' {err} m n ρ = refl
dup-comp' {ok} m n ρ with ⟦ m ⟧c ρ | inspect (⟦ m ⟧c) ρ 
dup-comp' {ok} m n ρ | just x | Reveal_is_.[ eq ] rewrite lemmaC (x , ρ) here m | eq = cong just (lemma-ctrC (x , ρ) here n) 
dup-comp' {ok} m n ρ | nothing | _  = refl
dup-comp' {errok} m n ρ with ⟦ m ⟧c ρ | inspect (⟦ m ⟧c) ρ 
dup-comp' {errok} m n ρ | just x | Reveal_is_.[ eq ] rewrite lemmaC (x , ρ) here m | eq = lemma-ctrC (x , ρ) here n
dup-comp' {errok} m n ρ | nothing | _ = refl



