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
--    LAM : ∀ σ {ε τ} → CTerm (σ ∷ Γ) (ε / τ) → VTerm Γ (σ ⇒ ε / τ)
    LAM : ∀ σ {τ} → CTerm (σ ∷ Γ) τ → VTerm Γ (σ ⇒ τ)    
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
  infer-effect (FST f $ _) = {!!}
  infer-effect (SND f $ _) = {!!}
  infer-effect (VAR x $ _) = {!!}
  infer-effect (LAM σ x $ _) = infer-effect x
--  infer-effect (PREC _ t t') = {!!}
  infer-effect (LET t IN t') = infer-effect t · infer-effect t'

  infer-comp : (σ : vType) → cTerm [] (// σ) → CType
  infer-comp σ (VAL x) = ok / infer-vtype σ {VAL x}
  infer-comp σ FAIL = err / infer-vtype  σ
  infer-comp σ (TRY c WITH c') = infer-effect c ⊔ infer-effect c' / infer-vtype σ
  infer-comp σ (IF _ THEN c ELSE c') = infer-effect c ⊔ infer-effect c' / infer-vtype σ
  infer-comp σ (FST f $ _) = {!!}
  infer-comp σ (SND f $ _) = {!!}
  infer-comp σ (VAR () $ x) 
  infer-comp σ₁ (LAM σ x $ _) = infer-effect x / infer-vtype σ
  infer-comp σ (LET c IN c') = infer-effect c · infer-effect c' / infer-vtype σ

  infer-vtype : (σ : vType) {c : cTerm [] (// σ)} → VType -- needs cTerm
  infer-vtype nat = nat
  infer-vtype bool = bool
  infer-vtype (t ∏ u) = infer-vtype  t ∏ infer-vtype  u
--  infer-vtype (t ⇒ // u) {c} = infer-vtype t  ⇒ infer-comp  u {!c!}
  infer-vtype (t ⇒ // u) {VAL x} = infer-vtype t  ⇒ ok / infer-vtype u 
  infer-vtype (t ⇒ // u) {FAIL} = {!!}
  infer-vtype (t ⇒ // u) {TRY c WITH c₁} = {!!}
  infer-vtype (t ⇒ // u) {IF x THEN c ELSE c₁} = {!!}
  infer-vtype (t ⇒ // u) {x $ x₁} = {!!}
  infer-vtype (t ⇒ // u) {LET c IN c₁} = {!!}
{-
  infer-ctx : Context → Ctx
  infer-ctx [] = []
  infer-ctx (σ ∷ γ) = infer-vtype  σ ∷ infer-ctx γ

  infer-var : (γ : Context) {σ : vType} (x : σ ∈ γ) → infer-vtype  σ ∈ (infer-ctx γ)
  infer-var [] ()
  infer-var (σ ∷ []) (here' refl) = {!!}
  infer-var (σ ∷ x ∷ γ) (here' refl) = {!!}
  infer-var (x' ∷ γ) (there p) = {!!}
  -}
  
  infer-vterm : {σ : vType} → vTerm [] σ → VTerm [] (infer-vtype  σ)
  infer-vterm  TT = TT
  infer-vterm  FF = FF
  infer-vterm  ZZ = ZZ
  infer-vterm  (SS v) = SS (infer-vterm  v)
  infer-vterm  ⟨ v , v' ⟩ = ⟨ infer-vterm v , infer-vterm  v' ⟩
  infer-vterm  (FST v) = FST (infer-vterm  v)
  infer-vterm  (SND v) = SND (infer-vterm  v)
  infer-vterm (VAR ()) --VAR {!!} --(infer-var  x)
  infer-vterm  (LAM σ x) = {!!}

  infer-ctype : {γ : Context} {σ : vType} → (c : cTerm γ (// σ)) → CType
  infer-ctype {γ} {σ} c = infer-effect c / infer-vtype σ
  
  infer : {σ : vType} → (c : cTerm [] (// σ)) → CTerm [] (infer-ctype c)
  infer (VAL x) = VAL (infer-vterm x)
  infer FAIL = FAIL
  infer (TRY c WITH c') = TRY infer  c WITH infer  c'
  infer (IF x THEN c ELSE c') = IF infer-vterm  x THEN infer  c ELSE infer  c'
  infer (f $ x) = {!!} --infer-vterm f $ infer-vterm x
--  infer γ (PREC x c c') = PREC (infer-vterm γ x) (infer γ c) {!!} {!!}
  infer (LET c IN c') = LET infer  c IN {!!} -- needs deeper context
