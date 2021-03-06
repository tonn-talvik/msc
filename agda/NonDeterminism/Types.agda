module Types where

open import Data.Maybe
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Grading
open import NonDetBoundedVec
open Grading.OrderedMonoid ℕ*
open Grading.GradedMonad NDBV

-- Types are parameterized over Effect dependent functions
-- Deciders: _⊑?_ _≡E?_
-- Bounds: _⊔_ _⊓_ ⊔-sym ⊓-sym
-- lub glb


infix  80 _/_
infixr 70 _⇒_
infix  60 _●_


mutual -- value and computation types
  data VType : Set where
    nat : VType
    bool : VType
    _●_ : VType → VType → VType
    _⇒_ : VType → CType → VType

  data CType : Set where
    _/_ : E → VType → CType

{-
-- really green types
data Type : Set where
  nat : Type
  bool : Type
  _π_ : Type → Type → Type
  _⇒_ : Type → Type → Type
-}



mutual -- subtyping of refined types
  data _≤V_ : VType → VType → Set where
    st-bn : bool ≤V nat
    st-refl : {σ : VType} → σ ≤V σ
    st-prod : {σ σ' τ τ' : VType} →
              σ ≤V σ' → τ ≤V τ' → σ ● τ ≤V σ' ● τ'
    st-func : {σ σ' : VType} {τ τ' : CType} →
              σ' ≤V σ → τ ≤C τ' →
              σ ⇒ τ ≤V σ' ⇒ τ'

  data _≤C_ : CType → CType → Set where
    st-comp : {e e' : E} {σ σ' : VType} →
              e ⊑ e' → σ ≤V σ' → e / σ ≤C e' / σ'


mutual -- subtype transitivity
  st-trans : {σ σ' σ'' : VType} → σ ≤V σ' → σ' ≤V σ'' → σ ≤V σ''
  st-trans st-refl q = q
  st-trans p st-refl = p
  st-trans (st-prod p p') (st-prod q q') = st-prod (st-trans p q)
                                                   (st-trans p' q')
  st-trans (st-func p p') (st-func q q') = st-func (st-trans q p)
                                                   (sct-trans p' q')

  sct-trans : {σ σ' σ'' : CType} → σ ≤C σ' → σ' ≤C σ'' → σ ≤C σ''
  sct-trans (st-comp p q) (st-comp p' q') = st-comp (⊑-trans p p')
                                                    (st-trans q q')


-------------------------------------------------------------

fst-≢  : {σ σ' τ τ' : VType} → ¬ σ ≡ σ' → ¬ σ ● τ ≡ σ' ● τ'
fst-≢ ¬p refl = ¬p refl

snd-≢  : {σ σ' τ τ' : VType} → ¬ τ ≡ τ' → ¬ σ ● τ ≡ σ' ● τ'
snd-≢ ¬q refl = ¬q refl

arg-≢ : {σ σ' : VType} {τ τ' : CType} → ¬ σ ≡ σ' → ¬ σ ⇒ τ ≡ σ' ⇒ τ'
arg-≢ ¬p refl = ¬p refl

cmp-≢  : {σ σ' : VType} {τ τ' : CType} → ¬ τ ≡ τ' → ¬ σ ⇒ τ ≡ σ' ⇒ τ'
cmp-≢ ¬p refl = ¬p refl

eff-≢  : {e e' : E} {σ σ' : VType} → ¬ e ≡ e' → ¬ e / σ ≡ e' / σ'
eff-≢ ¬p refl = ¬p refl

bdy-≢  : {e e' : E} {σ σ' : VType} → ¬ σ ≡ σ' → ¬ e / σ ≡ e' / σ'
bdy-≢ ¬p refl = ¬p refl


mutual -- equality deciders
  _≡V?_ : (σ σ' : VType) → Dec (σ ≡ σ')
  nat ≡V? nat = yes refl
  nat ≡V? bool = no (λ ())
  nat ≡V? (_ ● _) = no (λ ())  
  nat ≡V? (_ ⇒ _) = no (λ ())    
  bool ≡V? nat = no (λ ())
  bool ≡V? bool = yes refl
  bool ≡V? (_ ● _) = no (λ ())
  bool ≡V? (_ ⇒ _) = no (λ ())
  (_ ● _) ≡V? nat = no (λ ())
  (_ ● _) ≡V? bool = no (λ ())
  (σ ● σ') ≡V? (τ ● τ') with σ ≡V? τ | σ' ≡V? τ'
  (σ ● σ') ≡V? (.σ ● .σ') | yes refl | yes refl = yes refl
  ... | no ¬p | _     = no (fst-≢ ¬p)
  ... | _     | no ¬q = no (snd-≢ ¬q)
  (_ ● _) ≡V? (_ ⇒ _) = no (λ ())
  (_ ⇒ _) ≡V? nat = no (λ ())
  (_ ⇒ _) ≡V? bool = no (λ ())
  (_ ⇒ _) ≡V? (_ ● _) = no (λ ())
  (σ ⇒ τ) ≡V? (σ' ⇒ τ') with σ ≡V? σ' | τ ≡C? τ'
  (σ ⇒ τ) ≡V? (.σ ⇒ .τ) | yes refl | yes refl = yes refl
  ... | no ¬p | _     = no (arg-≢ ¬p)
  ... | _     | no ¬q = no (cmp-≢ ¬q)
  
  _≡C?_ : (τ τ' : CType) → Dec (τ ≡ τ')
  (e / σ) ≡C? (e' / σ') with e ≡E? e' | σ ≡V? σ'
  (e / σ) ≡C? (.e / .σ) | yes refl | yes refl = yes refl
  ... | no ¬p | _     = no (eff-≢ ¬p)
  ... | _     | no ¬q = no (bdy-≢ ¬q)

------------------------------------------------------------------------------

fst-≰V : {σ σ' τ τ' : VType} → ¬ σ ≤V σ' → ¬ σ ● τ ≤V σ' ● τ'
fst-≰V {σ} {.σ} ¬p st-refl = ¬p st-refl
fst-≰V ¬p (st-prod p _) =  ¬p p

snd-≰V : {σ σ' τ τ' : VType} → ¬ τ ≤V τ' → ¬ σ ● τ ≤V σ' ● τ'
snd-≰V {σ} {.σ} ¬q st-refl = ¬q st-refl
snd-≰V ¬q (st-prod _ q) =  ¬q q

arg-≰V : {σ σ' : VType} {τ τ' : CType} → ¬ σ' ≤V σ → ¬ σ ⇒ τ ≤V σ' ⇒ τ'
arg-≰V ¬p st-refl = ¬p st-refl
arg-≰V ¬p (st-func q q') = ¬p q

cmp-≰V  : {σ σ' : VType} {τ τ' : CType} → ¬ τ ≤C τ' → ¬ σ ⇒ τ ≤V σ' ⇒ τ'
cmp-≰V {τ = _ / _} ¬p st-refl = ¬p (st-comp ⊑-refl st-refl)
cmp-≰V ¬p (st-func q q') = ¬p q'

eff-≰C : {e e' : E} {σ σ' : VType} → ¬ e ⊑ e' → ¬ e / σ ≤C e' / σ'
eff-≰C ¬p (st-comp p _) = ¬p p

bdy-≰C : {e e' : E} {σ σ' : VType} → ¬ σ ≤V σ' → ¬ e / σ ≤C e' / σ'
bdy-≰C ¬q (st-comp _ q) = ¬q q

mutual -- inequality deciders
  _≤V?_ : (σ σ' : VType) → Dec (σ ≤V σ')
  nat ≤V? nat = yes st-refl
  nat ≤V? bool = no ( λ ())
  nat ≤V? (_ ● _) = no (λ ())
  nat ≤V? (_ ⇒ _) = no (λ ())
  bool ≤V? nat = yes st-bn
  bool ≤V? bool = yes st-refl
  bool ≤V? _ ● _ = no (λ ())
  bool ≤V? _ ⇒ _ = no (λ ())
  _ ● _ ≤V? nat = no (λ ())
  _ ● _ ≤V? bool = no (λ ())
  σ ● σ' ≤V? τ ● τ' with σ ≤V? τ | σ' ≤V? τ'
  ... | yes p | yes q = yes (st-prod p q)
  ... | no ¬p | _     = no (fst-≰V ¬p)
  ... | _     | no ¬q = no (snd-≰V ¬q)
  _ ● _ ≤V? _ ⇒ _ = no (λ ())
  (_ ⇒ _) ≤V? nat = no (λ ())
  (_ ⇒ _) ≤V? bool = no (λ ())
  (_ ⇒ _) ≤V? (σ' ● σ'') = no (λ ())
  (σ ⇒ τ) ≤V? (σ' ⇒ τ') with σ' ≤V? σ | τ ≤C? τ'
  ... | yes p | yes q = yes (st-func p q)
  ... | no ¬p | _     = no (arg-≰V ¬p)
  ... | _     | no ¬q = no (cmp-≰V ¬q)

  _≤C?_ : (τ τ' : CType) → Dec (τ ≤C τ')
  (e / σ) ≤C? (e' / σ') with e ⊑? e' | σ ≤V? σ'
  ... | yes p | yes q = yes (st-comp p q)
  ... | no ¬p | _     = no (eff-≰C ¬p)
  ... | _     | no ¬q = no (bdy-≰C ¬q)

---------------------------------------------------------------------

mutual -- greatest lower bound and least upper bound of VType, CType
  _⊓V_ : VType → VType → Maybe VType
  nat ⊓V nat = just nat
  nat ⊓V bool = just bool
  nat ⊓V _ = nothing
  bool ⊓V nat = just bool
  bool ⊓V bool = just bool
  bool ⊓V _ = nothing
  (σ ● τ) ⊓V (σ' ● τ') with σ ⊓V σ' | τ ⊓V τ'
  ... | just l | just r = just (l ● r)
  ... | _      | _      = nothing
  (σ ● τ) ⊓V _ = nothing
  (σ ⇒ τ) ⊓V (σ' ⇒ τ') with σ ⊔V σ' | τ ⊓C τ'
  ... | just v | just c = just (v ⇒ c)
  ... | _      | _      = nothing
  (σ ⇒ τ) ⊓V _ = nothing
  
  _⊓C_ : CType → CType → Maybe CType
  (e / σ) ⊓C (e' / σ') with e ⊓ e' | σ ⊓V σ'
  ... | ε | just v = just (ε / v)
  ... | _      | _ = nothing

  _⊔V_ : VType → VType → Maybe VType
  nat ⊔V nat = just nat
  nat ⊔V bool = just nat
  nat ⊔V _  = nothing
  bool ⊔V bool = just bool
  bool ⊔V nat = just nat
  bool ⊔V _    = nothing
  (σ ● τ) ⊔V (σ' ● τ') with σ ⊔V σ' | τ ⊔V τ'
  ... | just l | just r = just (l ● r)
  ... | _      | _      = nothing
  (σ ● σ') ⊔V _         = nothing
  (σ ⇒ τ) ⊔V (σ' ⇒ τ') with σ ⊓V σ' | τ ⊔C τ'
  ... | just v | just c = just (v ⇒ c)
  ... | _      | _      = nothing
  (σ ⇒ τ) ⊔V _ = nothing

  _⊔C_ : CType → CType → Maybe CType
  (e / σ) ⊔C (e' / σ') with σ ⊔V σ'
  ... | just v = just ((e ⊔ e') / v)
  ... | _      = nothing
mutual
  ⊔V-sym : (σ σ' : VType) → σ ⊔V σ' ≡ σ' ⊔V σ
  ⊔V-sym nat nat = refl
  ⊔V-sym nat bool = refl
  ⊔V-sym nat (_ ● _) = refl
  ⊔V-sym nat (_ ⇒ _) = refl
  ⊔V-sym bool nat = refl
  ⊔V-sym bool bool = refl
  ⊔V-sym bool (_ ● _) = refl
  ⊔V-sym bool (_ ⇒ _) = refl
  ⊔V-sym (_ ● _) nat = refl
  ⊔V-sym (_ ● _) bool = refl
  ⊔V-sym (σ ● τ) (σ' ● τ') with σ ⊔V σ' | τ ⊔V τ' | ⊔V-sym σ σ' | ⊔V-sym τ τ'
  ... | _ | _ | refl | refl = refl
  ⊔V-sym (_ ● _) (_ ⇒ _) = refl
  ⊔V-sym (_ ⇒ _) nat = refl
  ⊔V-sym (_ ⇒ _) bool = refl
  ⊔V-sym (_ ⇒ _) (_ ● _) = refl
  ⊔V-sym (σ ⇒ τ) (σ' ⇒ τ') with σ ⊓V σ' | τ ⊔C τ' | ⊓V-sym σ σ' | ⊔C-sym τ τ'
  ... | _ | _ | refl | refl = refl

  ⊔C-sym : (τ τ' : CType) → τ ⊔C τ' ≡ τ' ⊔C τ
  ⊔C-sym (e / σ) (e' / σ') with σ ⊔V σ' | σ' ⊔V σ | ⊔V-sym σ σ' -- DUNNO: why the symmetry here?
  ⊔C-sym (e / σ) (e' / σ') | just x | just .x | refl  = cong (λ ε → just (ε / x)) (⊔-sym e e')
  ⊔C-sym (e / σ) (e' / σ') | just _ | nothing | ()
  ⊔C-sym (e / σ) (e' / σ') | nothing | nothing | refl = refl

  ⊓V-sym : (σ σ' : VType) → σ ⊓V σ' ≡ σ' ⊓V σ
  ⊓V-sym nat nat = refl
  ⊓V-sym nat bool = refl
  ⊓V-sym nat (_ ● _) = refl
  ⊓V-sym nat (_ ⇒ _) = refl
  ⊓V-sym bool nat = refl
  ⊓V-sym bool bool = refl
  ⊓V-sym bool (_ ● _) = refl
  ⊓V-sym bool (_ ⇒ _) = refl
  ⊓V-sym (_ ● _) nat = refl
  ⊓V-sym (_ ● _) bool = refl
  ⊓V-sym (σ ● τ) (σ' ● τ') with σ ⊓V σ' | τ ⊓V τ' | ⊓V-sym σ σ' | ⊓V-sym τ τ'
  ... | _ | _ | refl | refl = refl
  ⊓V-sym (_ ● _) (_ ⇒ _) = refl
  ⊓V-sym (_ ⇒ _) nat = refl
  ⊓V-sym (_ ⇒ _) bool = refl
  ⊓V-sym (_ ⇒ _) (_ ● _) = refl
  ⊓V-sym (σ ⇒ τ) (σ' ⇒ τ') with σ ⊔V σ' | τ ⊓C τ' | ⊔V-sym σ σ' | ⊓C-sym τ τ'
  ... | _ | _ | refl | refl = refl

  ⊓C-sym : (τ τ' : CType) → τ ⊓C τ' ≡ τ' ⊓C τ
  ⊓C-sym (e / σ) (e' / σ') with e ⊓ e' | e' ⊓ e | σ ⊓V σ' | σ' ⊓V σ | ⊓-sym e e' | ⊓V-sym σ σ'
  ... | _ | _ | _ | _ | refl | refl = refl

_⊹C_ : CType → CType → Maybe CType
(e / σ) ⊹C (e' / σ') with σ ⊔V σ'
... | just v = just ((e ⊹ e') / v)
... | _      = nothing

mutual -- construct inequality proof from given lower and upper bound
  lbV : (σ σ' : VType) → {τ : VType} → σ ⊓V σ' ≡ just τ → τ ≤V σ
  lbV nat nat refl = st-refl
  lbV nat bool refl = st-bn
  lbV nat (_ ● _) ()
  lbV nat (_ ⇒ _) ()
  lbV bool nat refl = st-refl
  lbV bool bool refl = st-refl
  lbV bool (_ ● _) ()
  lbV bool (_ ⇒ _) ()
  lbV (_ ● _) nat ()
  lbV (_ ● _) bool ()
  lbV (σ ● σ') (τ ● τ') p with σ ⊓V τ | inspect (_⊓V_ σ) τ | σ' ⊓V τ' | inspect (_⊓V_ σ') τ'
  lbV (σ ● σ') (τ ● τ') refl | just _ | [ q ] | just _ | [ q' ] = st-prod (lbV σ τ q) (lbV σ' τ' q')
  lbV (σ ● σ') (τ ● τ') () | just _  | _ | nothing | _
  lbV (σ ● σ') (τ ● τ') () | nothing | _ | _       | _
  lbV (_ ● _) (_ ⇒ _) ()
  lbV (_ ⇒ _) nat ()
  lbV (_ ⇒ _) bool ()
  lbV (_ ⇒ _) (σ' ● σ'') ()
  lbV (σ ⇒ τ) (σ' ⇒ τ') p with σ ⊔V σ' | inspect (_⊔V_ σ) σ' | τ ⊓C τ' | inspect (_⊓C_ τ) τ'
  lbV (σ ⇒ τ) (σ' ⇒ τ') refl | just _ | [ q ] | just _ | [ q' ] = st-func (ubV σ σ' q) (lbC τ τ' q')
  lbV (σ ⇒ τ) (σ' ⇒ τ') () | just _  | _ | nothing | _
  lbV (σ ⇒ τ) (σ' ⇒ τ') () | nothing | _ | _       | _

  lbC : (τ τ' : CType) → {τ'' : CType} → τ ⊓C τ' ≡ just τ'' → τ'' ≤C τ
  lbC (e / σ) (e' / σ') p with e ⊓ e' | inspect (_⊓_ e) e' | σ ⊓V σ' | inspect (_⊓V_ σ) σ'
  lbC (e / σ) (e' / σ') refl | _ | [ refl ] | just x | [ q' ] = st-comp (glb e e') (lbV σ σ' q')
  lbC (e / σ) (e' / σ') () | _  | _ | nothing | _
  
  ubV : (σ σ' : VType) → {τ : VType} → σ ⊔V σ' ≡ just τ → σ ≤V τ 
  ubV nat nat refl = st-refl
  ubV nat bool refl = st-refl 
  ubV nat (_ ● _) ()
  ubV nat (_ ⇒ _) ()
  ubV bool nat refl = st-bn
  ubV bool bool refl = st-refl
  ubV bool (_ ● _) ()
  ubV bool (_ ⇒ _) ()
  ubV (_ ● _) nat ()
  ubV (_ ● _) bool ()
  ubV (σ ● σ') (τ ● τ') p with σ ⊔V τ | inspect (_⊔V_ σ) τ | σ' ⊔V τ' | inspect (_⊔V_ σ') τ'
  ubV (σ ● σ') (τ ● τ') refl | just _ | [ q ] | just _ | [ q' ] = st-prod (ubV σ τ q) (ubV σ' τ' q')
  ubV (σ ● σ') (τ ● τ') () | just _  | _ | nothing | _
  ubV (σ ● σ') (τ ● τ') () | nothing | _ | _       | _
  ubV (_ ● _) (_ ⇒ _) ()
  ubV (_ ⇒ _) nat ()
  ubV (_ ⇒ _) bool ()
  ubV (_ ⇒ _) (_ ● _) ()
  ubV (σ ⇒ τ) (σ' ⇒ τ') p with σ ⊓V σ' | inspect (_⊓V_ σ) σ' | τ ⊔C τ' | inspect (_⊔C_ τ) τ'
  ubV (σ ⇒ τ) (σ' ⇒ τ') refl | just _ | [ q ] | just _ | [ q' ] = st-func (lbV σ σ' q) (ubC τ τ' q')
  ubV (σ ⇒ τ) (σ' ⇒ τ') () | just _  | _ | nothing | _
  ubV (σ ⇒ τ) (σ' ⇒ τ') () | nothing | _ | _       | _

  ubC : (τ τ' : CType) → {τ'' : CType} → τ ⊔C τ' ≡ just τ'' → τ ≤C τ''
  ubC (e / σ) (e' / σ') p with σ ⊔V σ' | inspect (_⊔V_ σ) σ'
  ubC (e / σ) (e' / σ') refl | just x | [ q ] = st-comp (lub e e') (ubV σ σ' q)
  ubC (e / σ) (e' / σ') () | nothing | _


