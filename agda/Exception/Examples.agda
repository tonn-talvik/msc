{-# OPTIONS --type-in-type #-}
module Examples where

open import Data.Bool hiding (T)
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Finiteness
open import Raw
open import Types
open import Refined
open import Inference
open import Semantics

open import Exception
open import Grading
open Grading.GradedMonad ExcEffGM
open Grading.OrderedMonoid ExcEffOM

open import Optimization

-- example valua and computation terms
ADD : vTerm
ADD = LAM nat
          (VAL (LAM nat
                    (PREC (VAR 0)
                          (VAL (VAR 1))
                          (VAL (SS (VAR 0))))))

ADD-3-and-4 : cTerm
ADD-3-and-4 = LET ADD $ (SS (SS (SS ZZ)))
              IN VAR 0 $ (SS (SS (SS (SS ZZ))))

BAD-ONE : cTerm
BAD-ONE = ZZ $ TT

CMPLX : cTerm
CMPLX = LET TRY
               IF VAR 0
               THEN VAL (VAR 0)
               ELSE FAIL nat
            WITH VAL ZZ
        IN VAL (VAR 1)

SMPL : cTerm
SMPL = VAL (VAR 0)

CMPLX2 : cTerm
CMPLX2 = LET TRY
               IF VAR 0
               THEN VAL (VAR 0)
               ELSE FAIL nat
            WITH VAL ZZ
         IN (VAR 2) $ (VAR 1)
        
SMPL2 : cTerm
SMPL2 = (VAR 1) $ (VAR 0)

------------------------------------------
-- type inference

typing-add : infer-vtype [] ADD ≡ just (nat ⇒ ok / (nat ⇒ ok / nat))
typing-add = refl

typing-add-3-and-4 : infer-ctype [] ADD-3-and-4 ≡ just (ok / nat)
typing-add-3-and-4 = refl

typing-bad-one : infer-ctype [] BAD-ONE ≡ nothing
typing-bad-one = refl

Γ₀ = [ bool ]

Γ2 = bool ∷ bool ⇒ errok / bool ∷ []

typing-cmplx : infer-ctype Γ₀ CMPLX ≡ just (ok / bool)
typing-cmplx = refl

typing-smpl : infer-ctype Γ₀ SMPL ≡ just (ok / bool)
typing-smpl = refl

typing-cmplx2 : infer-ctype Γ2 CMPLX2 ≡ just (ok · errok / bool)
typing-cmplx2 = refl

----------------------------------------------
-- term refinment

refine-add = refine-vterm [] ADD
refine-add-3-and-4 = refine-cterm [] ADD-3-and-4

sem-add = ⟦ refine-add ⟧V tt
sem-add-3-and-4 = ⟦ refine-add-3-and-4 ⟧C tt

cmplx-refined = refine-cterm Γ₀ CMPLX -- = ... complex ...
smpl-refined = refine-cterm Γ₀ SMPL  -- = VAL (VAR (here' refl))

-- optimization
cmplx-smpl : {ρ : ⟪ Γ₀ ⟫X} →
            ⟦ refine-cterm Γ₀ CMPLX ⟧C ρ ≡ ⟦ refine-cterm Γ₀ SMPL ⟧C ρ
cmplx-smpl = refl -- degenerate dead computation

cmplx-smpl2 : {ρ : ⟪ Γ2 ⟫X} →
            ⟦ refine-cterm Γ2 CMPLX2 ⟧C ρ
            ≡ ⟦ refine-cterm Γ2 SMPL2 ⟧C ρ
cmplx-smpl2 = refl
-------------------------------------
--- some other examples

raw1 raw2 raw3 : cTerm
raw1 = IF FF THEN VAL ZZ ELSE (FAIL nat)
raw2 = IF (VAR 0) THEN (FAIL nat) ELSE (FAIL nat)
raw3 = LET VAL ZZ IN VAL (SS ZZ)

ref1 : refined-cterm [] raw1
ref1 = refine-cterm [] raw1
ref2 = refine-cterm [ bool ] raw2
ref3 = refine-cterm [] raw3

sem1 = ⟦ ref1 ⟧C tt
sem2 = ⟦ ref2 ⟧C (true , tt)
sem3 = ⟦ ref3 ⟧C tt

ss = ⟦ VAL (SS ZZ) ⟧C tt

p : sem3 ≡ ss
p = refl

pp : ⟦ ref3 ⟧C ≡ ⟦ VAL (SS ZZ) ⟧C
pp = refl

⟦_⟧' : (t : cTerm) (Γ : Ctx) {τ : CType} → {p : infer-ctype Γ t ≡ just τ} → ⟪ Γ ⟫X  → ⟪ τ ⟫C
⟦_⟧' t Γ {p = p} with infer-ctype Γ t | refine-cterm Γ t
⟦_⟧' t Γ {p = refl} | just τ | t' = ⟦ t' ⟧C
⟦_⟧' t Γ {p = ()} | nothing | t'


--------------------------------

foo-raw : cTerm
foo-raw = (VAR 0) $ ZZ

good-raw : cTerm
good-raw = LET (VAR 0) $ ZZ
           IN LET (VAR 1) $ ZZ
              IN VAL ⟨ VAR 0 , VAR 1 ⟩
better-raw : cTerm
better-raw = LET (VAR 0) $ ZZ
             IN VAL ⟨ VAR 0 , VAR 0 ⟩
good-Γ = [ nat ⇒ errok / nat ]

good-typing : infer-ctype good-Γ good-raw ≡ just (errok / (nat ● nat))
good-typing = refl
better-typing : infer-ctype good-Γ better-raw ≡ just (errok / (nat ● nat))
better-typing = refl

{-
optimize : (ρ : ⟪ good-Γ ⟫X) →
           ⟦ refine-cterm good-Γ good-raw ⟧C ρ ≡ ⟦ refine-cterm good-Γ better-raw ⟧C ρ
optimize ρ = dup-comp {!!} ({!!}) ρ
-}
