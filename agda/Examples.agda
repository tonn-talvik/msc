module Examples where
open import Data.Unit renaming (tt to top)
open import MyLanguage

-- bind function to variable
mul2 : ∀ {Γ} → CTerm Γ (nat ⇒ nat ⇒ nat)
mul2 = lam nat (lam nat
         (LET (lam nat
                      (prec (var here)
                            (val (var (there (there here))))
                            (lam nat (lam nat (val (ss (var here)))))))
            IN prec (var (there here))
                    (val zz)
                    (lam nat (lam nat (val (var (there (there here)))
                                            $ var here)))))
p-mul2-3-4 = ⟦ mul2 $ natify 3 $ natify 4 ⟧ top

-- use partially applied function
mul3 : ∀ {Γ} → CTerm Γ (nat ⇒ nat ⇒ nat)
mul3 = lam nat (lam nat
         (LET (lam nat
                      (prec (var here)
                            (val (var (there (there here))))
                            (lam nat (lam nat (val (ss (var here)))))))
            IN prec (var (there here))
                    (val zz)
                    (lam nat (val (var (there here))))))

p-mul3-3-4 = ⟦ mul3 $ natify 3 $ natify 4 ⟧ top


fact : ∀ {Γ} → CTerm Γ (nat ⇒ nat)
fact = lam nat
           (prec (var here)
                 (val (ss zz))
                 (lam nat
                      (lam nat
                           mul $ var (there here)
                               $ var here)))
                               



p-fact-5 = ⟦ fact $ natify 5 ⟧ top

is-zero : ∀ {Γ} → CTerm Γ (nat ⇒ bool)
is-zero = lam nat
              (prec (var here) (val tt) (lam nat (lam bool (val ff))))
p-is-zero = ⟦ is-zero $ natify 0 ⟧ top

inc dec : ∀ {Γ} → CTerm Γ (nat ⇒ nat)
inc = lam nat (val (ss (var here)))
dec = lam nat (LET prec (var here) (val ⟨ zz , tt ⟩)
                              (lam nat (lam (nat ∏ bool)
                                 if snd (var here) then
                                   val ⟨ zz , ff ⟩
                                 else
                                   val ⟨ ss (fst (var here)) , ff ⟩ fi))
                   IN val (fst (var here)) )
p-dec = ⟦ dec $ natify 10 ⟧ top

AND OR : ∀ {Γ} → CTerm Γ (bool ⇒ bool ⇒ bool)
AND = lam bool (lam bool
        if var here then
          if var (there here) then
            val tt
          else
            val ff
          fi
        else
          val ff
        fi)

OR = lam bool (lam bool if var here then val tt else if var (there here) then val tt else val ff fi fi)
NOT : ∀ {Γ} → CTerm Γ (bool ⇒ bool)
NOT = lam bool (if var here then val ff else val tt fi)
p-and = ⟦ AND $ tt $ ff ⟧ top


-- infinite program in my language
-- inf : ∀ {Γ} → CTerm Γ nat
-- inf = LET inf IN val (var here)
