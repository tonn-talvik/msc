{-# OPTIONS --type-in-type #-}

module ELanguage where

open import Data.Unit
open import Data.Nat hiding ( _⊓_ ; _⊔_ ) 
open import Data.Fin
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
--open Reveal_·_is_
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


mutual -- subtype transitivity
  st-trans : {σ σ' σ'' : VType} → σ ≤V σ' → σ' ≤V σ'' → σ ≤V σ''
  st-trans st-refl q = q
  -- st-trans st-bn st-refl = st-bn -- NOTE: this line is eaten by following line
  st-trans p st-refl = p
  st-trans (st-prod p p') (st-prod q q') = st-prod (st-trans p q) (st-trans p' q')
  st-trans (st-func p p') (st-func q q') = st-func (st-trans q p) (sct-trans p' q')

  sct-trans : {σ σ' σ'' : CType} → σ ≤C σ' → σ' ≤C σ'' → σ ≤C σ''
  sct-trans (st-comp p q) (st-comp p' q') = st-comp (⊑-trans p p') (st-trans q q')

mutual -- greatest lower bound and least upper bound of VType, CType
  _⊓V_ : VType → VType → Maybe VType
  nat ⊓V nat = just nat
  nat ⊓V bool = just bool
  nat ⊓V _ = nothing
  bool ⊓V nat = just bool
  bool ⊓V bool = just bool
  bool ⊓V _ = nothing
  (σ ∏ τ) ⊓V (σ' ∏ τ') with σ ⊓V σ' | τ ⊓V τ'
  ... | just l | just r = just (l ∏ r)
  ... | _      | _      = nothing
  (σ ∏ τ) ⊓V _ = nothing
  (σ ⟹ τ) ⊓V (σ' ⟹ τ') with σ ⊔V σ' | τ ⊓C τ'
  ... | just v | just c = just (v ⟹ c)
  ... | _      | _      = nothing
  (σ ⟹ τ) ⊓V _ = nothing
  
  _⊓C_ : CType → CType → Maybe CType
  (e / σ) ⊓C (e' / σ') with e ⊓ e' | σ ⊓V σ'
  ... | just ε | just v = just (ε / v)
  ... | _      | _ = nothing

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
  (σ ⟹ τ) ⊔V (σ' ⟹ τ') with σ ⊓V σ' | τ ⊔C τ'
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

{-
mutual -- construct inequality proof from given lower and upper bound
  lbV : (σ σ' : VType) → {τ : VType} → σ ⊓V σ' ≡ just τ → τ ≤V σ
  lbV nat nat refl = st-refl
  lbV nat bool refl = st-bn
  lbV nat (_ ∏ _) ()
  lbV nat (_ ⟹ _) ()
  lbV bool nat refl = st-refl
  lbV bool bool refl = st-refl
  lbV bool (_ ∏ _) ()
  lbV bool (_ ⟹ _) ()
  lbV (_ ∏ _) nat ()
  lbV (_ ∏ _) bool ()
  lbV (σ ∏ σ') (τ ∏ τ') p with σ ⊓V τ | inspect (_⊓V_ σ) τ | σ' ⊓V τ' | inspect (_⊓V_ σ') τ'
  lbV (σ ∏ σ') (τ ∏ τ') refl | just _ | [ q ] | just _ | [ q' ] = st-prod (lbV σ τ q) (lbV σ' τ' q')
  lbV (σ ∏ σ') (τ ∏ τ') () | just _  | _ | nothing | _
  lbV (σ ∏ σ') (τ ∏ τ') () | nothing | _ | _       | _
  lbV (_ ∏ _) (_ ⟹ _) ()
  lbV (_ ⟹ _) nat ()
  lbV (_ ⟹ _) bool ()
  lbV (_ ⟹ _) (σ' ∏ σ'') ()
  lbV (σ ⟹ τ) (σ' ⟹ τ') p with σ ⊔V σ' | inspect (_⊔V_ σ) σ' | τ ⊓C τ' | inspect (_⊓C_ τ) τ'
  lbV (σ ⟹ τ) (σ' ⟹ τ') refl | just _ | [ q ] | just _ | [ q' ] = st-func (ubV σ σ' q) (lbC τ τ' q')
  lbV (σ ⟹ τ) (σ' ⟹ τ') () | just _  | _ | nothing | _
  lbV (σ ⟹ τ) (σ' ⟹ τ') () | nothing | _ | _       | _

  lbC : (τ τ' : CType) → {τ'' : CType} → τ ⊓C τ' ≡ just τ'' → τ'' ≤C τ
  lbC (e / σ) (e' / σ') p with e ⊓ e' | inspect (_⊓_ e) e' | σ ⊓V σ' | inspect (_⊓V_ σ) σ'
  lbC (e / σ) (e' / σ') refl | just _ | [ q ] | just x | [ q' ] = st-comp (glb e e' q) (lbV σ σ' q')
  lbC (e / σ) (e' / σ') () | just _  | _ | nothing | _
  lbC (e / σ) (e' / σ') () | nothing | _ | _ | _
  
  ubV : (σ σ' : VType) → {τ : VType} → σ ⊔V σ' ≡ just τ → σ ≤V τ 
  ubV nat nat refl = st-refl
  ubV nat bool refl = st-refl 
  ubV nat (_ ∏ _) ()
  ubV nat (_ ⟹ _) ()
  ubV bool nat refl = st-bn
  ubV bool bool refl = st-refl
  ubV bool (_ ∏ _) ()
  ubV bool (_ ⟹ _) ()
  ubV (_ ∏ _) nat ()
  ubV (_ ∏ _) bool ()
  ubV (σ ∏ σ') (τ ∏ τ') p with σ ⊔V τ | inspect (_⊔V_ σ) τ | σ' ⊔V τ' | inspect (_⊔V_ σ') τ'
  ubV (σ ∏ σ') (τ ∏ τ') refl | just _ | [ q ] | just _ | [ q' ] = st-prod (ubV σ τ q) (ubV σ' τ' q')
  ubV (σ ∏ σ') (τ ∏ τ') () | just _  | _ | nothing | _
  ubV (σ ∏ σ') (τ ∏ τ') () | nothing | _ | _       | _
  ubV (_ ∏ _) (_ ⟹ _) ()
  ubV (_ ⟹ _) nat ()
  ubV (_ ⟹ _) bool ()
  ubV (_ ⟹ _) (_ ∏ _) ()
  ubV (σ ⟹ τ) (σ' ⟹ τ') p with σ ⊓V σ' | inspect (_⊓V_ σ) σ' | τ ⊔C τ' | inspect (_⊔C_ τ) τ'
  ubV (σ ⟹ τ) (σ' ⟹ τ') refl | just _ | [ q ] | just _ | [ q' ] = st-func (lbV σ σ' q) (ubC τ τ' q')
  ubV (σ ⟹ τ) (σ' ⟹ τ') () | just _  | _ | nothing | _
  ubV (σ ⟹ τ) (σ' ⟹ τ') () | nothing | _ | _       | _

  ubC : (τ τ' : CType) → {τ'' : CType} → τ ⊔C τ' ≡ just τ'' → τ ≤C τ''
  ubC (e / σ) (e' / σ') p with σ ⊔V σ' | inspect (_⊔V_ σ) σ'
  ubC (e / σ) (e' / σ') refl | just x | [ q ] = st-comp (lub e e') (ubV σ σ' q)
  ubC (e / σ) (e' / σ') () | nothing | _


--ubV' : (σ σ' : VType) → (λ {(just τ) → σ ≤V τ ; (nothing) → ⊤} ) (σ ⊔V σ' )
--ubV' = {!!}

mutual
  ⊔V-sym : (σ σ' : VType) → σ ⊔V σ' ≡ σ' ⊔V σ
  ⊔V-sym nat nat = refl
  ⊔V-sym nat bool = refl
  ⊔V-sym nat (_ ∏ _) = refl
  ⊔V-sym nat (_ ⟹ _) = refl
  ⊔V-sym bool nat = refl
  ⊔V-sym bool bool = refl
  ⊔V-sym bool (_ ∏ _) = refl
  ⊔V-sym bool (_ ⟹ _) = refl
  ⊔V-sym (_ ∏ _) nat = refl
  ⊔V-sym (_ ∏ _) bool = refl
  ⊔V-sym (σ ∏ τ) (σ' ∏ τ') with σ ⊔V σ' | τ ⊔V τ' | ⊔V-sym σ σ' | ⊔V-sym τ τ'
  ... | _ | _ | refl | refl = refl
  ⊔V-sym (_ ∏ _) (_ ⟹ _) = refl
  ⊔V-sym (_ ⟹ _) nat = refl
  ⊔V-sym (_ ⟹ _) bool = refl
  ⊔V-sym (_ ⟹ _) (_ ∏ _) = refl
  ⊔V-sym (σ ⟹ τ) (σ' ⟹ τ') with σ ⊓V σ' | τ ⊔C τ' | ⊓V-sym σ σ' | ⊔C-sym τ τ'
  ... | _ | _ | refl | refl = refl

  ⊔C-sym : (τ τ' : CType) → τ ⊔C τ' ≡ τ' ⊔C τ
  ⊔C-sym (e / σ) (e' / σ') with σ ⊔V σ' | σ' ⊔V σ | ⊔V-sym σ σ' -- FIXME: why the symmetry here?
  ⊔C-sym (e / σ) (e' / σ') | just x | just .x | refl  = cong (λ ε → just (ε / x)) (⊔-sym e e')
  ⊔C-sym (e / σ) (e' / σ') | just _ | nothing | ()
  ⊔C-sym (e / σ) (e' / σ') | nothing | nothing | refl = refl

  ⊓V-sym : (σ σ' : VType) → σ ⊓V σ' ≡ σ' ⊓V σ
  ⊓V-sym nat nat = refl
  ⊓V-sym nat bool = refl
  ⊓V-sym nat (_ ∏ _) = refl
  ⊓V-sym nat (_ ⟹ _) = refl
  ⊓V-sym bool nat = refl
  ⊓V-sym bool bool = refl
  ⊓V-sym bool (_ ∏ _) = refl
  ⊓V-sym bool (_ ⟹ _) = refl
  ⊓V-sym (_ ∏ _) nat = refl
  ⊓V-sym (_ ∏ _) bool = refl
  ⊓V-sym (σ ∏ τ) (σ' ∏ τ') with σ ⊓V σ' | τ ⊓V τ' | ⊓V-sym σ σ' | ⊓V-sym τ τ'
  ... | _ | _ | refl | refl = refl
  ⊓V-sym (_ ∏ _) (_ ⟹ _) = refl
  ⊓V-sym (_ ⟹ _) nat = refl
  ⊓V-sym (_ ⟹ _) bool = refl
  ⊓V-sym (_ ⟹ _) (_ ∏ _) = refl
  ⊓V-sym (σ ⟹ τ) (σ' ⟹ τ') with σ ⊔V σ' | τ ⊓C τ' | ⊔V-sym σ σ' | ⊓C-sym τ τ'
  ... | _ | _ | refl | refl = refl

  ⊓C-sym : (τ τ' : CType) → τ ⊓C τ' ≡ τ' ⊓C τ
  ⊓C-sym (e / σ) (e' / σ') with e ⊓ e' | e' ⊓ e | σ ⊓V σ' | σ' ⊓V σ | ⊓-sym e e' | ⊓V-sym σ σ'
  ... | _ | _ | _ | _ | refl | refl = refl
  -}
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
    FAIL : (σ : VType) → CTerm' Γ (err / σ)
    --TRY_WITH_ : ∀ {e e' σ} → CTerm' Γ (e / σ) → CTerm' Γ (e' / σ) → CTerm' Γ (e ⊔ e' / σ)
    TRY_WITH_ : ∀ {e e' σ} → CTerm' Γ (e / σ) → CTerm' Γ (e' / σ) → CTerm' Γ (e ⊹ e' / σ) 
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
    FAIL : (σ : VType) → CTerm Γ (just (err / σ))
    TRY_WITH_ : ∀ {e e' σ} → CTerm Γ (just (e / σ)) → CTerm Γ (just (e' / σ)) → CTerm Γ (just (e ⊹ e' / σ))
    --TRY_WITH_ : ∀ {τ τ'} → CTerm Γ (just τ) → CTerm Γ (just τ') → CTerm Γ (τ ⊹C τ')    
--    IF_THEN_ELSE_ : ∀ {e e' σ} → VTerm Γ (just bool) → CTerm Γ (just (e / σ)) → CTerm Γ (just (e' / σ)) → CTerm Γ (e / σ ⊔C e' / σ)
    IF_THEN_ELSE_ : ∀ {e e' σ} → VTerm Γ (just bool) → CTerm Γ (just (e / σ)) → CTerm Γ (just (e' / σ)) → CTerm Γ (just (e ⊔ e' / σ))    
    _$_ : {σ : VType} {τ : CType} → VTerm Γ (just (σ ⟹ τ)) → VTerm Γ (just σ) → CTerm Γ (just τ)
--    PREC : ∀ {e' e'' σ} → VTerm Γ nat → CTerm Γ (e'' / σ) →
--           CTerm (σ ∷ nat ∷ Γ) (e' / σ) → e'' · e' ⊑ e'' → CTerm Γ (e'' / σ)
    LET_IN_ : ∀ {e e' σ σ'} → CTerm Γ (just (e / σ)) → CTerm (σ ∷ Γ) (just (e' / σ')) → CTerm Γ (just (e · e' / σ'))
    CCAST :  ∀ {e e' σ σ'} → CTerm Γ (just (e / σ)) → e / σ ≤C e' / σ' → CTerm Γ (just (e' / σ'))


---------------------------------------------------------------

mutual
  dropT : (Γ : Ctx) → {σ : VType} → (x : σ ∈ Γ) → Ctx
  dropT .(x' ∷ xs) (here' {x'} {xs} x) = xs
  dropT .(x' ∷ xs) (there {x'} {xs} x) = x' ∷ dropT xs x 

  wkvar : {Γ : Ctx} → {σ : VType} → (x : σ ∈ Γ)  → {τ : VType}
     → τ ∈ dropT Γ x → τ ∈ Γ
  wkvar (here' refl) y = there y
  wkvar (there x) (here' refl) = here' refl
  wkvar (there x) (there y) = there (wkvar x y)


  wkV : {Γ : Ctx} {σ τ : VType} → (x : σ ∈ Γ) → VTerm' (dropT Γ x) τ → VTerm' Γ τ
  wkV x TT = TT
  wkV x FF = FF
  wkV x ZZ = ZZ
  wkV x (SS t) = SS (wkV x t)
  wkV x ⟨ t , t₁ ⟩ = ⟨ wkV x t , wkV x t₁ ⟩
  wkV x (FST t) = FST (wkV x t)
  wkV x (SND t) = SND (wkV x t)
  wkV x (VAR x') = VAR (wkvar x x')
  wkV x (LAM σ t) = LAM σ (wkC (there x) t)
  wkV x (VCAST t p) = VCAST (wkV x t) p

  
  wkC : {Γ : Ctx} {σ : VType} {τ : CType}  (x : σ ∈ Γ) → CTerm' (dropT Γ x) τ → CTerm' Γ τ
  wkC x (VAL y) = VAL (wkV x y) 
  wkC x (FAIL σ₁) = FAIL σ₁
  wkC x (TRY t WITH u) = TRY (wkC x t) WITH (wkC x u)
  wkC x (IF b THEN t ELSE u) = IF (wkV x b) THEN (wkC x t) ELSE (wkC x u)
  wkC x (t $ u) = wkV x t $ wkV x u
  wkC x (LET t IN u) = LET (wkC x t) IN (wkC (there x) u)
  wkC x (CCAST t p) = CCAST (wkC x t) p 

{-

  ctrV : {Γ : Ctx} {σ τ : VType} → VTerm' (σ ∷ σ ∷ Γ) τ → VTerm' (σ ∷ Γ) τ
  ctrV TT = TT
  ctrV FF = FF
  ctrV ZZ = {!!}
  ctrV (SS t) = SS (ctrV t)
  ctrV ⟨ t , t₁ ⟩ = {!!}
  ctrV (FST t) = {!!}
  ctrV (SND t) = {!!}
  ctrV (VAR (here' x)) =  VAR (here' x)
  ctrV (VAR (there x)) =  VAR x
  ctrV (LAM σ₁ x) = {!!}
  ctrV (VCAST t x) = {!!}

  ctrC : {Γ : Ctx} {σ : VType} {τ : CType} → CTerm' (σ ∷ σ ∷ Γ) τ → CTerm' (σ ∷ Γ) τ
  ctrC (VAL x) = {!!}
  ctrC (FAIL σ₁) = {!!}
  ctrC (TRY t WITH t₁) = {!!}
  ctrC (IF x THEN t ELSE t₁) = {!!}
  ctrC (x $ x₁) = {!!}
  ctrC (LET t IN t₁) = {!!}
  ctrC (CCAST t x) = {!!}

-}

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
    FAIL : (σ : VType) → cTerm Γ (// (erase-vtype σ))
    TRY_WITH_ : ∀ {σ} → cTerm Γ σ → cTerm Γ σ → cTerm Γ σ
    IF_THEN_ELSE_ : ∀ {σ} → vTerm Γ bool → cTerm Γ σ → cTerm Γ σ → cTerm Γ σ
    _$_ : {σ : vType} {τ : cType} → vTerm Γ (σ ⇒ τ) → vTerm Γ σ → cTerm Γ (τ)    
--    _$_ : ∀ {σ τ} → vTerm Γ (σ ⇒ // τ) → vTerm Γ σ → cTerm Γ (// τ)
--    PREC : ∀ {σ} → vTerm Γ nat → cTerm Γ σ →
--           cTerm (σ ∷ nat ∷ Γ) σ → cTerm Γ σ
    LET_IN_ : ∀ {σ σ'} → cTerm Γ (// (erase-vtype σ)) → cTerm (σ ∷ Γ) σ' → cTerm Γ σ'
--    CCAST :  ∀ {e e' σ σ'} → CTerm Γ (e / σ) → e / σ ⟪ e' / σ' → CTerm Γ (e' / σ')


-----------------------------------------------------------------------




------------------------------------------------------------------------

fst-≢  : {σ σ' τ τ' : VType} → ¬ σ ≡ σ' → ¬ σ ∏ τ ≡ σ' ∏ τ'
fst-≢ ¬p refl = ¬p refl

snd-≢  : {σ σ' τ τ' : VType} → ¬ τ ≡ τ' → ¬ σ ∏ τ ≡ σ' ∏ τ'
snd-≢ ¬q refl = ¬q refl

arg-≢ : {σ σ' : VType} {τ τ' : CType} → ¬ σ ≡ σ' → ¬ σ ⟹ τ ≡ σ' ⟹ τ'
arg-≢ ¬p refl = ¬p refl

cmp-≢  : {σ σ' : VType} {τ τ' : CType} → ¬ τ ≡ τ' → ¬ σ ⟹ τ ≡ σ' ⟹ τ'
cmp-≢ ¬p refl = ¬p refl

eff-≢  : {e e' : Exc} {σ σ' : VType} → ¬ e ≡ e' → ¬ e / σ ≡ e' / σ'
eff-≢ ¬p refl = ¬p refl

bdy-≢  : {e e' : Exc} {σ σ' : VType} → ¬ σ ≡ σ' → ¬ e / σ ≡ e' / σ'
bdy-≢ ¬p refl = ¬p refl


mutual -- equality deciders
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
  ... | no ¬p | _     = no (fst-≢ ¬p)
  ... | _     | no ¬q = no (snd-≢ ¬q)
  (_ ∏ _) ≡V? (_ ⟹ _) = no (λ ())
  (_ ⟹ _) ≡V? nat = no (λ ())
  (_ ⟹ _) ≡V? bool = no (λ ())
  (_ ⟹ _) ≡V? (_ ∏ _) = no (λ ())
  (σ ⟹ τ) ≡V? (σ' ⟹ τ') with σ ≡V? σ' | τ ≡C? τ'
  (σ ⟹ τ) ≡V? (.σ ⟹ .τ) | yes refl | yes refl = yes refl
  ... | no ¬p | _     = no (arg-≢ ¬p)
  ... | _     | no ¬q = no (cmp-≢ ¬q)
  
  _≡C?_ : (τ τ' : CType) → Dec (τ ≡ τ')
  (e / σ) ≡C? (e' / σ') with e ≡E? e' | σ ≡V? σ'
  (e / σ) ≡C? (.e / .σ) | yes refl | yes refl = yes refl
  ... | no ¬p | _     = no (eff-≢ ¬p)
  ... | _     | no ¬q = no (bdy-≢ ¬q)



fst-≰V : {σ σ' τ τ' : VType} → ¬ σ ≤V σ' → ¬ σ ∏ τ ≤V σ' ∏ τ'
fst-≰V {σ} {.σ} ¬p st-refl = ¬p st-refl
fst-≰V ¬p (st-prod p _) =  ¬p p

snd-≰V : {σ σ' τ τ' : VType} → ¬ τ ≤V τ' → ¬ σ ∏ τ ≤V σ' ∏ τ'
snd-≰V {σ} {.σ} ¬q st-refl = ¬q st-refl
snd-≰V ¬q (st-prod _ q) =  ¬q q

arg-≰V : {σ σ' : VType} {τ τ' : CType} → ¬ σ' ≤V σ → ¬ σ ⟹ τ ≤V σ' ⟹ τ'
arg-≰V ¬p st-refl = ¬p st-refl
arg-≰V ¬p (st-func q q') = ¬p q

cmp-≰V  : {σ σ' : VType} {τ τ' : CType} → ¬ τ ≤C τ' → ¬ σ ⟹ τ ≤V σ' ⟹ τ'
cmp-≰V {τ = _ / _} ¬p st-refl = ¬p (st-comp ⊑-refl st-refl)
cmp-≰V ¬p (st-func q q') = ¬p q'

eff-≰C : {e e' : Exc} {σ σ' : VType} → ¬ e ⊑ e' → ¬ e / σ ≤C e' / σ'
eff-≰C ¬p (st-comp p _) = ¬p p

bdy-≰C : {e e' : Exc} {σ σ' : VType} → ¬ σ ≤V σ' → ¬ e / σ ≤C e' / σ'
bdy-≰C ¬q (st-comp _ q) = ¬q q

mutual -- inequality deciders
  _≤V?_ : (σ σ' : VType) → Dec (σ ≤V σ')
  nat ≤V? nat = yes st-refl
  nat ≤V? bool = no ( λ ())
  nat ≤V? (_ ∏ _) = no (λ ())
  nat ≤V? (_ ⟹ _) = no (λ ())
  bool ≤V? nat = yes st-bn
  bool ≤V? bool = yes st-refl
  bool ≤V? _ ∏ _ = no (λ ())
  bool ≤V? _ ⟹ _ = no (λ ())
  _ ∏ _ ≤V? nat = no (λ ())
  _ ∏ _ ≤V? bool = no (λ ())
  σ ∏ σ' ≤V? τ ∏ τ' with σ ≤V? τ | σ' ≤V? τ'
  ... | yes p | yes q = yes (st-prod p q)
  ... | no ¬p | _     = no (fst-≰V ¬p)
  ... | _     | no ¬q = no (snd-≰V ¬q)
  _ ∏ _ ≤V? _ ⟹ _ = no (λ ())
  (_ ⟹ _) ≤V? nat = no (λ ())
  (_ ⟹ _) ≤V? bool = no (λ ())
  (_ ⟹ _) ≤V? (σ' ∏ σ'') = no (λ ())
  (σ ⟹ τ) ≤V? (σ' ⟹ τ') with σ' ≤V? σ | τ ≤C? τ'
  ... | yes p | yes q = yes (st-func p q)
  ... | no ¬p | _     = no (arg-≰V ¬p)
  ... | _     | no ¬q = no (cmp-≰V ¬q)

  _≤C?_ : (τ τ' : CType) → Dec (τ ≤C τ')
  (e / σ) ≤C? (e' / σ') with e ⊑? e' | σ ≤V? σ'
  ... | yes p | yes q = yes (st-comp p q)
  ... | no ¬p | _     = no (eff-≰C ¬p)
  ... | _     | no ¬q = no (bdy-≰C ¬q)

