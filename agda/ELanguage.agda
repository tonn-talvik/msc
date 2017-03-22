{-# OPTIONS --type-in-type #-}

module ELanguage where

open import Data.Unit
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; cong; subst)
open import Relation.Nullary

open import Exception
open import Finiteness
open import OrderedMonoid
open OrderedMonoid.OrderedMonoid ExcEffOM


infixl 90 _$_
infix  80 _/_
infixr 70 _⇒_ _⟹_
infix  60 _∏_

------------------------------------------------------------  
-- refined types and language

mutual -- value and computation types
  data VType : Set where
    nat : VType
    bool : VType
    _∏_ : VType → VType → VType
    _⟹_ : VType → CType → VType

  data CType : Set where
    _/_ : Exc → VType → CType


mutual -- subtyping of refined types
  data _≤V_ : VType → VType → Set where
    st-bn : bool ≤V nat
    st-refl : {σ : VType} → σ ≤V σ
--    st-trans : {σ σ' σ'' : VType} → σ ≤V σ' → σ' ≤V σ'' → σ ≤V σ''
    st-prod : {σ σ' τ τ' : VType} → σ ≤V σ' → τ ≤V τ' → σ ∏ τ ≤V σ' ∏ τ'
    st-func : {σ σ' : VType} {τ τ' : CType} →
              σ' ≤V σ → τ ≤C τ' →
              σ ⟹ τ ≤V σ' ⟹ τ'

  data _≤C_ : CType → CType → Set where
    st-comp : {e e' : E} {σ σ' : VType} → e ⊑ e' → σ ≤V σ' → e / σ ≤C e' / σ'


mutual 
  st-trans : {σ σ' σ'' : VType} → σ ≤V σ' → σ' ≤V σ'' → σ ≤V σ''
  st-trans st-bn st-refl = st-bn
  st-trans st-refl q = q
  st-trans (st-prod p p₁) st-refl = st-prod p p₁
  st-trans (st-prod p p₁) (st-prod q q₁) = st-prod (st-trans p q) (st-trans p₁ q₁)
  st-trans (st-func p p₁) st-refl = st-func p p₁
  st-trans (st-func p p₁) (st-func q q₁) = st-func (st-trans q p) (sct-trans p₁ q₁)

  sct-trans : {σ σ' σ'' : CType} → σ ≤C σ' → σ' ≤C σ'' → σ ≤C σ''
  sct-trans p q = {!!}

mutual -- least upper bound of VType and CType
  _⊔V_ : VType → VType → Maybe VType
  nat ⊔V nat = just nat
  nat ⊔V bool = just nat
  nat ⊔V _  = nothing
  bool ⊔V bool = just bool
  bool ⊔V nat = just nat
  bool ⊔V _    = nothing
  (σ ∏ τ) ⊔V (σ' ∏ τ') with σ ⊔V σ' | τ ⊔V τ'
  ... | just l | just r = just (l ∏ r)
  ... | _      | _      = nothing
  (σ ∏ σ') ⊔V _         = nothing
  (σ ⟹ τ) ⊔V (σ' ⟹ τ') with σ ⊔V σ' | τ ⊔C τ'
  ... | just v | just c = just (v ⟹ c)
  ... | _      | _      = nothing
  (σ ⟹ τ) ⊔V _ = nothing

  _⊔C_ : CType → CType → Maybe CType
  (e / σ) ⊔C (e' / σ') with σ ⊔V σ'
  ... | just v = just (e ⊔ e' / v)
  ... | _      = nothing

  _⊹C_ : CType → CType → Maybe CType
  (e / σ) ⊹C (e' / σ') with σ ⊔V σ'
  ... | just v = just (e ⊹ e' / v)
  ... | _      = nothing
  


--data Inspect {A : Set}(x : A) : Set where
--  it : (y : A) -> x ≡ y -> Inspect x

--inspect : {A : Set}(x : A) -> Inspect x
--inspect x = it x refl

ubV' : (σ σ' : VType) → {τ : VType} → σ ⊔V σ' ≡ just τ → σ ≤V τ 
ubV' nat nat refl = st-refl
ubV' nat bool refl = st-refl 
ubV' nat (σ' ∏ σ'') ()
ubV' nat (σ' ⟹ x) ()
ubV' bool nat refl = st-bn
ubV' bool bool refl = st-refl
ubV' bool (σ' ∏ σ'') p = {!!}
ubV' bool (σ' ⟹ x) p = {!!}
ubV' (σ ∏ σ₁) nat p = {!!}
ubV' (σ ∏ σ₁) bool p = {!!}
ubV' (σ ∏ σ₁) (σ' ∏ σ'') p with inspect (σ ⊔V σ') | inspect (σ₁ ⊔V σ'') 
ubV' (σ ∏ σ₁) (σ' ∏ σ'') refl | it (just x) q  | it (just x₁) r = st-prod (ubV' σ σ' {!q!}) {!!} 
ubV' (σ ∏ σ₁) (σ' ∏ σ'') () | _ | nothing
ubV' (σ ∏ σ₁) (σ' ∏ σ'') () | nothing | _
ubV' (σ ∏ σ₁) (σ' ⟹ x) ()
ubV' (σ ⟹ x) σ' p = {!!} 

--ubV : (σ σ' : VType) → (λ {(just τ) → σ ≤V τ ; (nothing) → ⊤} ) σ ⊔V σ' 
--ubV = ?

Ctx = List VType


mutual -- value and computation terms

  data VTerm' (Γ : Ctx) : VType → Set where
    TT FF : VTerm' Γ bool
    ZZ : VTerm' Γ nat
    SS : VTerm' Γ nat → VTerm' Γ nat
    ⟨_,_⟩ : {σ σ' : VType} → VTerm' Γ σ → VTerm' Γ σ' → VTerm' Γ (σ ∏ σ')
    FST : {σ σ' : VType} → VTerm' Γ (σ ∏ σ') → VTerm' Γ σ
    SND : {σ σ' : VType} → VTerm' Γ (σ ∏ σ') → VTerm' Γ σ'
    VAR : {σ : VType} → σ ∈ Γ → VTerm' Γ σ
--    LAM : (σ : VType) {ε : E} {τ : VType} → CTerm' (σ ∷ Γ) (ε / τ) → VTerm' Γ (σ ⇒ ε / τ)
    LAM : (σ : VType) {τ : CType} → CTerm' (σ ∷ Γ) τ → VTerm' Γ (σ ⟹ τ)    
    VCAST : {σ σ' : VType} → VTerm' Γ σ → σ ≤V σ' → VTerm' Γ σ'

  data CTerm' (Γ : Ctx) : CType → Set where
    VAL : {σ : VType} → VTerm' Γ σ → CTerm' Γ (ok / σ)
    FAIL : {σ : VType} → CTerm' Γ (err / σ)
    TRY_WITH_ : ∀ {e e' σ} → CTerm' Γ (e / σ) → CTerm' Γ (e' / σ) → CTerm' Γ (e ⊔ e' / σ)
    IF_THEN_ELSE_ : ∀ {e e' σ} → VTerm' Γ bool → CTerm' Γ (e / σ) → CTerm' Γ (e' / σ) → CTerm' Γ (e ⊔ e' / σ)
    _$_ : {σ : VType} {τ : CType} → VTerm' Γ (σ ⟹ τ) → VTerm' Γ σ → CTerm' Γ τ
--    PREC : ∀ {e' e'' σ} → VTerm' Γ nat → CTerm' Γ (e'' / σ) →
--           CTerm' (σ ∷ nat ∷ Γ) (e' / σ) → e'' · e' ⊑ e'' → CTerm' Γ (e'' / σ)
    LET_IN_ : ∀ {e e' σ σ'} → CTerm' Γ (e / σ) → CTerm' (σ ∷ Γ) (e' / σ') → CTerm' Γ (e · e' / σ')
    CCAST :  ∀ {e e' σ σ'} → CTerm' Γ (e / σ) → e / σ ≤C e' / σ' → CTerm' Γ (e' / σ')


  data VTerm (Γ : Ctx) : Maybe VType → Set where
    TT FF : VTerm Γ (just bool)
    ZZ : VTerm Γ (just nat)
    SS : VTerm Γ (just nat) → VTerm Γ (just nat)
    ⟨_,_⟩ : {σ σ' : VType} → VTerm Γ (just σ) → VTerm Γ (just σ') → VTerm Γ (just (σ ∏ σ'))
    FST : {σ σ' : VType} → VTerm Γ (just (σ ∏ σ')) → VTerm Γ (just σ)
    SND : {σ σ' : VType} → VTerm Γ (just (σ ∏ σ')) → VTerm Γ (just σ')
    VAR : {σ : VType} → σ ∈ Γ → VTerm Γ (just σ)
--    LAM : (σ : VType) {ε : E} {τ : VType} → CTerm (σ ∷ Γ) (ε / τ) → VTerm Γ (σ ⇒ ε / τ)
    LAM : (σ : VType) {τ : CType} → CTerm (σ ∷ Γ) (just τ) → VTerm Γ (just (σ ⟹ τ))
    VCAST : {σ σ' : VType} → VTerm Γ (just σ) → σ ≤V σ' → VTerm Γ (just σ')

  data CTerm (Γ : Ctx) : Maybe CType → Set where
    VAL : {σ : VType} → VTerm Γ (just σ) → CTerm Γ (just (ok / σ))
    FAIL : {σ : VType} → CTerm Γ (just (err / σ))
    TRY_WITH_ : ∀ {e e' σ} → CTerm Γ (just (e / σ)) → CTerm Γ (just (e' / σ)) → CTerm Γ (just (e ⊹ e' / σ))
    --TRY_WITH_ : ∀ {τ τ'} → CTerm Γ (just τ) → CTerm Γ (just τ') → CTerm Γ (τ ⊹C τ')    
--    IF_THEN_ELSE_ : ∀ {e e' σ} → VTerm Γ (just bool) → CTerm Γ (just (e / σ)) → CTerm Γ (just (e' / σ)) → CTerm Γ (e / σ ⊔C e' / σ)
    IF_THEN_ELSE_ : ∀ {e e' σ} → VTerm Γ (just bool) → CTerm Γ (just (e / σ)) → CTerm Γ (just (e' / σ)) → CTerm Γ (just (e ⊔ e' / σ))    
    _$_ : {σ : VType} {τ : CType} → VTerm Γ (just (σ ⟹ τ)) → VTerm Γ (just σ) → CTerm Γ (just τ)
--    PREC : ∀ {e' e'' σ} → VTerm Γ nat → CTerm Γ (e'' / σ) →
--           CTerm (σ ∷ nat ∷ Γ) (e' / σ) → e'' · e' ⊑ e'' → CTerm Γ (e'' / σ)
    LET_IN_ : ∀ {e e' σ σ'} → CTerm Γ (just (e / σ)) → CTerm (σ ∷ Γ) (just (e' / σ')) → CTerm Γ (just (e · e' / σ'))
    CCAST :  ∀ {e e' σ σ'} → CTerm Γ (just (e / σ)) → e / σ ≤C e' / σ' → CTerm Γ (just (e' / σ'))



-----------------------------------------------------------
-- Raw types and language
mutual 
  data vType : Set where
    nat : vType
    bool : vType
    _π_ : vType → vType → vType
    _⇒_ : vType → cType → vType
  data cType : Set where
    // : vType → cType


mutual
  erase-vtype : VType → vType
  erase-vtype nat = nat
  erase-vtype bool = bool
  erase-vtype (σ ∏ σ') = erase-vtype σ π erase-vtype σ'
  erase-vtype (σ ⟹ σ') = erase-vtype σ ⇒ erase-ctype σ'

  erase-ctype : CType → cType
  erase-ctype (e / σ) = // (erase-vtype σ)



mutual -- value and computation terms
  data vTerm (Γ : Ctx) : vType → Set where
    TT FF : vTerm Γ bool
    ZZ : vTerm Γ nat
    SS : vTerm Γ nat → vTerm Γ nat
    ⟨_,_⟩ : {σ σ' : vType} → vTerm Γ σ → vTerm Γ σ' → vTerm Γ (σ π σ')
    FST : {σ σ' : vType} → vTerm Γ (σ π σ') → vTerm Γ σ
    SND : {σ σ' : vType} → vTerm Γ (σ π σ') → vTerm Γ σ'
    VAR : {σ : VType} → σ ∈ Γ → vTerm Γ (erase-vtype σ)
    LAM : (σ : VType) {τ : cType} → cTerm (σ ∷ Γ) τ → vTerm Γ ((erase-vtype σ) ⇒ τ)
--    VCAST : {σ σ' : vType} → VTerm Γ σ → σ ≤V σ' → VTerm Γ σ'

--  teistsugune LAM
--   LAM : (σ : VType) {τ : cType} → cTerm ((erase-vtype σ) ∷ γ) τ → vTerm γ ((erase-vtype σ) ⇒ τ)

  data cTerm (Γ : Ctx) : cType → Set where
    VAL : {σ : vType} → vTerm Γ σ → cTerm Γ (// σ)
    FAIL : {σ : vType} → cTerm Γ (// σ)
    TRY_WITH_ : ∀ {σ} → cTerm Γ σ → cTerm Γ σ → cTerm Γ σ
    IF_THEN_ELSE_ : ∀ {σ} → vTerm Γ bool → cTerm Γ σ → cTerm Γ σ → cTerm Γ σ
    _$_ : {σ : vType} {τ : cType} → vTerm Γ (σ ⇒ τ) → vTerm Γ σ → cTerm Γ (τ)    
--    _$_ : ∀ {σ τ} → vTerm Γ (σ ⇒ // τ) → vTerm Γ σ → cTerm Γ (// τ)
--    PREC : ∀ {σ} → vTerm Γ nat → cTerm Γ σ →
--           cTerm (σ ∷ nat ∷ Γ) σ → cTerm Γ σ
    LET_IN_ : ∀ {σ σ'} → cTerm Γ (// (erase-vtype σ)) → cTerm (σ ∷ Γ) σ' → cTerm Γ σ'
--    CCAST :  ∀ {e e' σ σ'} → CTerm Γ (e / σ) → e / σ ⟪ e' / σ' → CTerm Γ (e' / σ')



lemma : {σ σ' τ τ' : VType} → ¬ σ ≤V σ' → ¬ σ ∏ τ ≤V σ' ∏ τ'
lemma {σ} {.σ} ¬p st-refl = ¬p st-refl
lemma ¬p (st-prod p _) =  ¬p p

mutual -- subtyping of refined types isn't decidable, is it?
{-
  lemma-nat≰Vbool : ¬ (nat ≤V bool)
  lemma-nat≰Vbool (st-trans st-refl q) = lemma-nat≰Vbool q
  lemma-nat≰Vbool (st-trans (st-trans p p') st-refl) = lemma-nat≰Vbool (st-trans p p')
  lemma-nat≰Vbool (st-trans (st-trans {σ' = τ} p p') (st-trans {σ' = τ'} q q')) = {!!}
-}
  _≤V?_ : (σ σ' : VType) → Dec (σ ≤V σ')
  nat ≤V? nat = yes st-refl
  nat ≤V? bool = no ( λ ())
  nat ≤V? (σ' ∏ σ'') = no (λ ())
  nat ≤V? (σ' ⟹ x) = no (λ ())
  bool ≤V? nat = yes st-bn
  bool ≤V? bool = yes st-refl
  bool ≤V? σ' ∏ σ'' = no (λ ())
  bool ≤V? σ' ⟹ x = no (λ ())
  σ ∏ τ ≤V? nat = no (λ ())
  σ ∏ τ ≤V? bool = no (λ ())
  σ ∏ τ ≤V? σ' ∏ σ'' with σ ≤V? σ' 
  σ ∏ τ ≤V? σ' ∏ σ'' | yes p = {!!}
  σ ∏ τ ≤V? σ' ∏ σ'' | no ¬p = no (lemma ¬p) -- {! no (λ { (st-refl) → ¬p st-refl ; (st-prod p _) → ¬p p }) !} 
  σ ∏ τ ≤V? σ' ⟹ x = no (λ ())
  (σ ⟹ τ) ≤V? σ' = {!!}


open import Data.Empty
open import Function

proj-fst-≡ : {σ σ' τ τ' : VType} → σ ∏ τ ≡ σ' ∏ τ' → σ ≡ σ'
proj-fst-≡ refl = refl

proj-snd-≡ : {σ σ' τ τ' : VType} → σ ∏ τ ≡ σ' ∏ τ' → τ ≡ τ'
proj-snd-≡ refl = refl

proj-arg-≡ : {σ σ' : VType} {τ τ' : CType} → σ ⟹ τ ≡ σ' ⟹ τ' → σ ≡ σ'
proj-arg-≡ refl = refl

proj-cmp-≡ : {σ σ' : VType} {τ τ' : CType} → σ ⟹ τ ≡ σ' ⟹ τ' → τ ≡ τ'
proj-cmp-≡ refl = refl

proj-eff-≡ : {e e' : Exc} {σ σ' : VType} → e / σ ≡ e' / σ' → e ≡ e'
proj-eff-≡ refl = refl

proj-bdy-≡ : {e e' : Exc} {σ σ' : VType} → e / σ ≡ e' / σ' → σ ≡ σ'
proj-bdy-≡ refl = refl

-- this should be defined in Exception
_≡E?_ : (e e' : Exc) → Dec (e ≡ e')
err ≡E? err = yes refl
err ≡E? ok = no (λ ())
err ≡E? errok = no (λ ())
ok ≡E? err = no (λ ())
ok ≡E? ok = yes refl
ok ≡E? errok = no (λ ())
errok ≡E? err = no (λ ())
errok ≡E? ok = no (λ ())
errok ≡E? errok = yes refl

mutual
  _≡V?_ : (σ σ' : VType) → Dec (σ ≡ σ')
  nat ≡V? nat = yes refl
  nat ≡V? bool = no (λ ())
  nat ≡V? (_ ∏ _) = no (λ ())  
  nat ≡V? (_ ⟹ _) = no (λ ())    
  bool ≡V? nat = no (λ ())
  bool ≡V? bool = yes refl
  bool ≡V? (_ ∏ _) = no (λ ())
  bool ≡V? (_ ⟹ _) = no (λ ())
  (_ ∏ _) ≡V? nat = no (λ ())
  (_ ∏ _) ≡V? bool = no (λ ())
  (σ ∏ σ') ≡V? (τ ∏ τ') with σ ≡V? τ | σ' ≡V? τ'
  (σ ∏ σ') ≡V? (.σ ∏ .σ') | yes refl | yes refl = yes refl
  ... | no ¬p | _     = no (¬p ∘ proj-fst-≡)
  ... | _     | no ¬q = no (¬q ∘ proj-snd-≡)
  (_ ∏ _) ≡V? (_ ⟹ _) = no (λ ())
  (_ ⟹ _) ≡V? nat = no (λ ())
  (_ ⟹ _) ≡V? bool = no (λ ())
  (_ ⟹ _) ≡V? (_ ∏ _) = no (λ ())
  (σ ⟹ τ) ≡V? (σ' ⟹ τ') with σ ≡V? σ' | τ ≡C? τ'
  (σ ⟹ τ) ≡V? (.σ ⟹ .τ) | yes refl | yes refl = yes refl
  ... | no ¬p | _     = no (¬p ∘ proj-arg-≡)
  ... | _     | no ¬q = no (¬q ∘ proj-cmp-≡)
  
  _≡C?_ : (τ τ' : CType) → Dec (τ ≡ τ')
  (e / σ) ≡C? (e' / σ') with e ≡E? e' | σ ≡V? σ'
  (e / σ) ≡C? (.e / .σ) | yes refl | yes refl = yes refl
  ... | no ¬p | _     = no (¬p ∘ proj-eff-≡)
  ... | _     | no ¬q = no (¬q ∘ proj-bdy-≡)
