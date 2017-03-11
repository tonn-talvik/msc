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
    _$_ : ∀ {σ τ} → vTerm Γ (σ ⇒ τ) → vTerm Γ σ → cTerm Γ (τ)    
--    _$_ : ∀ {σ τ} → vTerm Γ (σ ⇒ // τ) → vTerm Γ σ → cTerm Γ (// τ)
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
--    LAM : ∀ σ {τ} → CTerm (σ ∷ Γ) τ → VTerm Γ (σ ⇒ τ)    
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

-----------------------------------------------------------
-- effect erasure

mutual
  erase-vtype : VType → vType
  erase-vtype nat = nat
  erase-vtype bool = bool
  erase-vtype (σ ∏ σ') = erase-vtype σ ∏ erase-vtype σ'
  erase-vtype (σ ⇒ σ') = erase-vtype σ ⇒ erase-ctype σ'

  erase-ctype : CType → cType
  erase-ctype (e / σ) = // (erase-vtype σ)

erase-ctx : Ctx → Context
erase-ctx [] = []
erase-ctx (σ ∷ Γ) = erase-vtype σ ∷ erase-ctx Γ

erase-var : {Γ : Ctx} {σ : VType} → σ ∈ Γ → erase-vtype σ ∈ erase-ctx Γ
erase-var (here' x) = here' (cong erase-vtype x)
erase-var (there p) = there (erase-var p)

mutual
  erase-vterm : {Γ : Ctx} {σ : VType} → VTerm Γ σ → vTerm (erase-ctx Γ) (erase-vtype σ)
  erase-vterm TT = TT
  erase-vterm FF = FF
  erase-vterm ZZ = ZZ
  erase-vterm (SS t) = SS (erase-vterm t)
  erase-vterm ⟨ t , t' ⟩ = ⟨ erase-vterm t , erase-vterm t' ⟩ 
  erase-vterm (FST t) = FST (erase-vterm t)
  erase-vterm (SND t) = SND (erase-vterm t)
  erase-vterm (VAR x) = VAR (erase-var x)
  erase-vterm (LAM σ x) = LAM (erase-vtype σ) (erase x)
  erase-vterm (VCAST t x) = {!!}

  erase : {Γ : Ctx} {τ : CType} → CTerm Γ τ → cTerm (erase-ctx Γ) (erase-ctype τ)
  erase (VAL x) = VAL (erase-vterm x)
  erase FAIL = FAIL
  erase (TRY t WITH t') = TRY erase t WITH erase t'
  erase (IF x THEN t ELSE t') = IF erase-vterm x THEN erase t ELSE erase t'
  erase (f $ x) = erase-vterm f $ erase-vterm x
  erase (LET t IN t') = LET erase t IN erase t'
  erase (CCAST c x) = {!!}




-- effect inference

get-func-body : {γ : Context} {σ : vType} {τ : cType} → vTerm γ (σ ⇒ τ) → {!τ!}
get-func-body = {!!}

mutual

  infer-effect : {γ : Context} {σ : cType} → cTerm γ σ → Exc
  infer-effect (VAL _) = ok
  infer-effect FAIL = err
  infer-effect (TRY t WITH t') = infer-effect t ⊔ infer-effect t'
  infer-effect (IF _ THEN t ELSE t') = infer-effect t ⊔ infer-effect t'
  {-
  infer-effect (FST ⟨ FST p , p' ⟩ $ x) = {!!}
  infer-effect (FST ⟨ SND p , p' ⟩ $ x) = {!!}
  infer-effect (FST ⟨ VAR x , p' ⟩ $ x₁) = {!!}
  infer-effect (FST ⟨ LAM σ x , p' ⟩ $ _) = infer-effect x
  infer-effect (FST (FST p) $ x) = {!!}
  infer-effect (FST (SND p) $ x) = {!!}
  infer-effect (FST (VAR x) $ x₁) = {!!} -- infer-effect (VAL f) -}
  infer-effect (FST f $ _) = {!!}
  infer-effect (SND f $ _) = {!!}
  infer-effect (VAR x $ _) = {!!}
  infer-effect (LAM σ x $ _) = infer-effect x
--  infer-effect (PREC _ t t') = {!!}
  infer-effect (LET t IN t') = infer-effect t · infer-effect t'

  infer-ctype : {γ : Context} (σ : vType) → cTerm γ (// σ) → CType
  infer-ctype σ (VAL x) = ok / infer-vtype σ {VAL x}
  infer-ctype σ FAIL = err / infer-vtype  σ
  infer-ctype σ (TRY c WITH c') = infer-effect c ⊔ infer-effect c' / infer-vtype σ
  infer-ctype σ (IF _ THEN c ELSE c') = infer-effect c ⊔ infer-effect c' / infer-vtype σ
  infer-ctype σ (FST f $ _) = {!!}
  infer-ctype σ (SND f $ _) = {!!}
  infer-ctype σ (VAR f $ x) = {!!}
  infer-ctype σ₁ (LAM σ x $ _) = infer-effect x / infer-vtype σ
  infer-ctype σ (LET c IN c') = infer-effect c · infer-effect c' / infer-vtype σ

  infer-vtype : {γ : Context} (σ : vType) {c : cTerm γ (// σ)} → VType -- needs cTerm
  infer-vtype nat = nat
  infer-vtype bool = bool
  infer-vtype (σ ∏ σ') = infer-vtype σ ∏ infer-vtype σ'
  infer-vtype (t ⇒ t') {c} = infer-vtype t ⇒ infer-ctype t {!!}

  infer-ctx : Context → Ctx
  infer-ctx [] = []
  infer-ctx (σ ∷ γ) = infer-vtype  σ ∷ infer-ctx γ

  infer-var : (γ : Context) {σ : vType} (x : σ ∈ γ) → infer-vtype  σ ∈ (infer-ctx γ)
  infer-var [] ()
  infer-var (σ ∷ []) (here' refl) = {!!}
  infer-var (σ ∷ x ∷ γ) (here' refl) = {!!}
  infer-var (x' ∷ γ) (there p) = {!!}
  
  infer-vterm : {γ : Context} {σ : vType} → vTerm γ σ → VTerm (infer-ctx γ) (infer-vtype σ)
  infer-vterm TT = TT
  infer-vterm FF = FF
  infer-vterm ZZ = ZZ
  infer-vterm (SS v) = SS (infer-vterm v)
  infer-vterm ⟨ v , v' ⟩ = ⟨ infer-vterm v , infer-vterm v' ⟩
  infer-vterm (FST v) = FST (infer-vterm v)
  infer-vterm (SND v) = SND (infer-vterm v)
  infer-vterm {γ} (VAR x) = VAR (infer-var γ x)
  infer-vterm (LAM σ x) = LAM (infer-vtype σ) (infer {!!})
  
  infer : {γ : Context} {σ : vType} → (c : cTerm γ (// σ)) → CTerm (infer-ctx γ) (infer-ctype σ c)
  infer (VAL x) = {!!} --VAL (infer-vterm x)
  infer FAIL = FAIL
  infer (TRY t WITH t') = {!!} --TRY infer t WITH infer t'
  infer (IF x THEN t ELSE t') = {!!} --IF infer-vterm  x THEN infer t ELSE infer t'
  infer (f $ x) = infer-vterm f $ infer-vterm x
--  infer γ (PREC x c c') = PREC (infer-vterm γ x) (infer γ c) {!!} {!!}
  infer (LET t IN t') = {!!} --LET infer t IN infer t'
