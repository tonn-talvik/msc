{-# OPTIONS --type-in-type #-}

module ELanguage where

open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; cong)

open import Exception
open import Finiteness
open import OrderedMonoid
open OrderedMonoid.OrderedMonoid ExcEffOM

infixl 90 _$_
infix  80 _/_
infixr 70 _⇒_
infix  60 _∏_

-----------------------------------------------------------
-- Raw types and language
mutual 
  data vType : Set where
    nat : vType
    bool : vType
    _∏_ : vType → vType → vType
    _⇒_ : vType → cType → vType
  data cType : Set where
    // : vType → cType


Context = List vType

mutual -- value and computation terms
  data vTerm (Γ : Context) : vType → Set where
    TT FF : vTerm Γ bool
    ZZ : vTerm Γ nat
    SS : vTerm Γ nat → vTerm Γ nat
    ⟨_,_⟩ : {σ σ' : vType} → vTerm Γ σ → vTerm Γ σ' → vTerm Γ (σ ∏ σ')
    FST : {σ σ' : vType} → vTerm Γ (σ ∏ σ') → vTerm Γ σ
    SND : {σ σ' : vType} → vTerm Γ (σ ∏ σ') → vTerm Γ σ'
    VAR : {σ : vType} → σ ∈ Γ → vTerm Γ σ
    LAM : ∀ σ {τ} → cTerm (σ ∷ Γ) τ → vTerm Γ (σ ⇒ τ)
--    VCAST : {σ σ' : vType} → VTerm Γ σ → σ ≤V σ' → VTerm Γ σ'

  data cTerm (Γ : Context) : cType → Set where
    VAL : {σ : vType} → vTerm Γ σ → cTerm Γ (// σ)
    FAIL : {σ : vType} → cTerm Γ (// σ)
    TRY_WITH_ : ∀ {σ} → cTerm Γ σ → cTerm Γ σ → cTerm Γ σ
    IF_THEN_ELSE_ : ∀ {σ} → vTerm Γ bool → cTerm Γ σ → cTerm Γ σ → cTerm Γ σ
    _$_ : ∀ {σ τ} → vTerm Γ (σ ⇒ // τ) → vTerm Γ σ → cTerm Γ (// τ)
--    PREC : ∀ {σ} → vTerm Γ nat → cTerm Γ σ →
--           cTerm (σ ∷ nat ∷ Γ) σ → cTerm Γ σ
    LET_IN_ : ∀ {σ σ'} → cTerm Γ (// σ) → cTerm (σ ∷ Γ) σ' → cTerm Γ σ'
--    CCAST :  ∀ {e e' σ σ'} → CTerm Γ (e / σ) → e / σ ⟪ e' / σ' → CTerm Γ (e' / σ')


------------------------------------------------------------  

mutual -- value and computation types
  data VType : Set where
    nat : VType
    bool : VType
    _∏_ : VType → VType → VType
    _⇒_ : VType → CType → VType

  data CType : Set where
    _/_ : Exc → VType → CType


mutual -- subtyping of refined types
  data _≤V_ : VType → VType → Set where
    st-refl : {σ : VType} → σ ≤V σ
    st-trans : {σ σ' σ'' : VType} → σ ≤V σ' → σ' ≤V σ'' → σ ≤V σ''
    st-prod : {σ σ' τ τ' : VType} → σ ≤V σ' → τ ≤V τ' → σ ∏ τ ≤V σ' ∏ τ'
    st-func : {σ σ' : VType} {c c' : CType} →
              σ' ≤V σ → c ⟪ c' →
              σ ⇒ c ≤V σ' ⇒ c'

  data _⟪_ : CType → CType → Set where
    st-comp : {e e' : E} {σ σ' : VType} → e ⊑ e' → σ ≤V σ' → e / σ ⟪ e' / σ'


Ctx = List VType


mutual -- value and computation terms
  data VTerm (Γ : Ctx) : VType → Set where
    TT FF : VTerm Γ bool
    ZZ : VTerm Γ nat
    SS : VTerm Γ nat → VTerm Γ nat
    ⟨_,_⟩ : {σ σ' : VType} → VTerm Γ σ → VTerm Γ σ' → VTerm Γ (σ ∏ σ')
    FST : {σ σ' : VType} → VTerm Γ (σ ∏ σ') → VTerm Γ σ
    SND : {σ σ' : VType} → VTerm Γ (σ ∏ σ') → VTerm Γ σ'
    VAR : {σ : VType} → σ ∈ Γ → VTerm Γ σ
    LAM : ∀ σ {ε τ} → CTerm (σ ∷ Γ) (ε / τ) → VTerm Γ (σ ⇒ ε / τ)
    VCAST : {σ σ' : VType} → VTerm Γ σ → σ ≤V σ' → VTerm Γ σ'

  data CTerm (Γ : Ctx) : CType → Set where
    VAL : {σ : VType} → VTerm Γ σ → CTerm Γ (ok / σ)
    FAIL : {σ : VType} → CTerm Γ (err / σ)
    TRY_WITH_ : ∀ {e e' σ} → CTerm Γ (e / σ) → CTerm Γ (e' / σ) → CTerm Γ (e ⊔ e' / σ)
    IF_THEN_ELSE_ : ∀ {e e' σ} → VTerm Γ bool → CTerm Γ (e / σ) → CTerm Γ (e' / σ) → CTerm Γ (e ⊔ e' / σ)
    _$_ : ∀ {σ τ} → VTerm Γ (σ ⇒ τ) → VTerm Γ σ → CTerm Γ τ
--    PREC : ∀ {e' e'' σ} → VTerm Γ nat → CTerm Γ (e'' / σ) →
--           CTerm (σ ∷ nat ∷ Γ) (e' / σ) → e'' · e' ⊑ e'' → CTerm Γ (e'' / σ)
    LET_IN_ : ∀ {e e' σ σ'} → CTerm Γ (e / σ) → CTerm (σ ∷ Γ) (e' / σ') → CTerm Γ (e · e' / σ')
    CCAST :  ∀ {e e' σ σ'} → CTerm Γ (e / σ) → e / σ ⟪ e' / σ' → CTerm Γ (e' / σ')

------------------------------------
-- effect inference


mutual

  infer-effect : {γ : Context} {σ : cType} → cTerm γ σ → Exc
  infer-effect (VAL _) = ok
  infer-effect FAIL = err
  infer-effect (TRY t WITH t') = infer-effect t ⊔ infer-effect t'
  infer-effect (IF _ THEN t ELSE t') = infer-effect t ⊔ infer-effect t'
  infer-effect (f $ _) = infer-effect {!!} --infer-effect {!!}
--  infer-effect (PREC _ t t') = {!!}
  infer-effect (LET t IN t') = infer-effect t · infer-effect t'

  infer-comp : (γ : Context) → (σ : vType) → cTerm γ (// σ) → CType
  infer-comp γ σ (VAL _) = ok / infer-vtype γ σ
  infer-comp γ σ FAIL = err / infer-vtype γ σ
  infer-comp γ σ (TRY c WITH c') = {!!}
  infer-comp γ σ (IF x THEN c ELSE c') = {!!}
  infer-comp γ _ (f $ x) = {!!}
  infer-comp γ σ (LET c IN c') = {!!}

  infer-vtype : Context → vType → VType -- needs cTerm
  infer-vtype γ nat = nat
  infer-vtype γ bool = bool
  infer-vtype γ (t ∏ u) = infer-vtype γ t ∏ infer-vtype γ u
  infer-vtype γ (t ⇒ // u) = infer-vtype γ t ⇒ infer-comp γ u {!!}

{-
  lemma-infer-vtype : (γ : List vType) (σ : vType) → infer-vtype γ σ ≡ infer-vtype (σ ∷ γ) σ
  lemma-infer-vtype γ nat = refl
  lemma-infer-vtype γ bool = refl
  lemma-infer-vtype γ (σ ∏ σ') = {!!}
  lemma-infer-vtype γ (σ ⇒ σ') = {!!}
-}

  infer-ctx : Context → Ctx
  infer-ctx [] = []
  infer-ctx (σ ∷ γ) = infer-vtype γ σ ∷ infer-ctx γ

  infer-var : (γ : Context) {σ : vType} (x : σ ∈ γ) → infer-vtype γ σ ∈ (infer-ctx γ)
  infer-var [] ()
  infer-var (σ ∷ []) (here' refl) = {!!}
  infer-var (σ ∷ x ∷ γ) (here' refl) = {!!} --here' (lemma-infer-vtype γ σ)
  infer-var (x' ∷ γ) (there p) = {!!}
  
  infer-vterm : (γ : Context) {σ : vType} → vTerm γ σ → VTerm (infer-ctx γ) (infer-vtype γ σ)
  infer-vterm γ TT = TT
  infer-vterm γ FF = FF
  infer-vterm γ ZZ = ZZ
  infer-vterm γ (SS v) = SS (infer-vterm γ v)
  infer-vterm γ ⟨ v , v' ⟩ = ⟨ infer-vterm γ v , infer-vterm γ v' ⟩
  infer-vterm γ (FST v) = FST (infer-vterm γ v)
  infer-vterm γ (SND v) = SND (infer-vterm γ v)
  infer-vterm γ (VAR x) = VAR (infer-var γ x)
  infer-vterm γ (LAM σ x) = {!!}

  infer-ctype : {γ : Context} {σ : vType} → (c : cTerm γ (// σ)) → CType
  infer-ctype {γ} {σ} c = infer-effect c / (infer-vtype γ σ)
  
  infer : (γ : Context) {σ : vType} → (c : cTerm γ (// σ)) → CTerm (infer-ctx γ) (infer-ctype c)
  infer γ (VAL x) = VAL (infer-vterm γ x)
  infer γ FAIL = FAIL
  infer γ (TRY c WITH c') = TRY infer γ c WITH infer γ c'
  infer γ (IF x THEN c ELSE c') = IF infer-vterm γ x THEN infer γ c ELSE infer γ c'
  infer γ (f $ x) = infer-vterm γ {!!} $ infer-vterm γ x
--  infer γ (PREC x c c') = PREC (infer-vterm γ x) (infer γ c) {!!} {!!}
  infer γ (LET c IN c') = LET infer γ c IN {!!}
