{-# OPTIONS --type-in-type #-}
module Examples where

open import Data.Bool hiding (T)
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Relation.Binary.Core

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

infer-add = refine-vterm [] ADD
infer-add-3-and-4 = refine-cterm [] ADD-3-and-4

sem-add = ⟦ infer-add ⟧v tt
sem-add-3-and-4 = ⟦ infer-add-3-and-4 ⟧c tt



raw1 raw2 raw3 : cTerm
raw1 = IF FF THEN VAL ZZ ELSE (FAIL nat)
raw2 = IF (VAR 0) THEN (FAIL nat) ELSE (FAIL nat)
raw3 = LET VAL ZZ IN VAL (SS ZZ)

ref1 : refined-cterm [] raw1
ref1 = refine-cterm [] raw1
ref2 = refine-cterm [ bool ] raw2
ref3 = refine-cterm [] raw3

sem1 = ⟦ ref1 ⟧c tt
sem2 = ⟦ ref2 ⟧c (true , tt)
sem3 = ⟦ ref3 ⟧c tt

ss = ⟦ VAL (SS ZZ) ⟧c tt

p : sem3 ≡ ss
p = refl

pp : ⟦ ref3 ⟧c ≡ ⟦ VAL (SS ZZ) ⟧c
pp = refl

⟦_⟧' : (t : cTerm) (Γ : Ctx) {τ : CType} → {p : infer-ctype Γ t ≡ just τ} → ⟪ Γ ⟫x  → ⟪ τ ⟫c
⟦_⟧' t Γ {p = p} with infer-ctype Γ t | refine-cterm Γ t
⟦_⟧' t Γ {p = refl} | just τ | t' = ⟦ t' ⟧c
⟦_⟧' t Γ {p = ()} | nothing | t'


--xxx : {e : Exc} → T e ℕ
--xxx = ⟦ raw3 ⟧ [] tt



