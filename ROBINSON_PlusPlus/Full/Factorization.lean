/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block8
import ROBINSON_PlusPlus.Full.Numerals
import ROBINSON_PlusPlus.Full.PrimeFactor

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block8

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Full

/-!
## FULL — Factorización (existencia) transferida al object

`tfa_exists_numeral` : todo `n ≥ 1` tiene una factorización prima **object**:
existe una lista meta de primos `ps` cuyo encoding object `toTerm ps`
(lista de pares `(numeral p, 1)`) cumple `prod_pairs (toTerm ps) = numeral n`.

La factorización se **computa en ℕ** (`primeFactorList`, `Full/PrimeFactor.lean`)
y se **transfiere** por el homomorfismo de numerales (`numeral_pow`,
`numeral_mul`, `prod_pairs` axiomas). La primalidad de cada factor se conserva
a nivel meta (en `ps`, vía `IsPrimeNat`) — lista para alimentar
`isPrime_numeral` cuando se quiera la forma de membership de Block8.

**Encoding**: exponente 1 con repetición (`prod_pairs [(p,1)…] = Π p`), que es
todo lo que la existencia necesita (no requiere primos distintos).
-/

/-- Encoding object de una lista meta de primos: lista de pares `(numeral p, 1)`. -/
def toTerm : List Nat → Term
  | []      => nil
  | p :: ps => cons (pair (numeral p) one) (toTerm ps)

@[simp] theorem toTerm_nil : toTerm [] = nil := rfl
@[simp] theorem toTerm_cons (p : Nat) (ps : List Nat) :
    toTerm (p :: ps) = cons (pair (numeral p) one) (toTerm ps) := rfl

/-- `prod_pairs (toTerm ps) =eq numeral (natProd ps)`. Por inducción meta en
    `ps`, usando los axiomas de `prod_pairs`, `numeral_pow` (p^1 = p) y
    `numeral_mul`. -/
theorem prod_pairs_toTerm (ps : List Nat) :
    axioms ⊢ (prod_pairs (toTerm ps) =eq numeral (natProd ps)) := by
  induction ps with
  | nil =>
    -- prod_pairs nil =eq one = numeral 1 = numeral (natProd [])
    exact prod_pairs_nil
  | cons p ps ih =>
    -- pow (numeral p) one =eq numeral p   (p^1 = p)
    have h_pow : axioms ⊢ (pow (numeral p) one =eq numeral p) := by
      have hp := numeral_pow p 1
      rw [Nat.pow_one] at hp
      exact hp
    -- cadena: prod_pairs(cons) =eq (numeral p)·(prod_pairs rest) =eq numeral (p · natProd ps)
    have c1 : axioms ⊢ (prod_pairs (cons (pair (numeral p) one) (toTerm ps)) =eq
                        mul (pow (numeral p) one) (prod_pairs (toTerm ps))) :=
      prod_pairs_cons (numeral p) one (toTerm ps)
    have c2 : axioms ⊢ (mul (pow (numeral p) one) (prod_pairs (toTerm ps)) =eq
                        mul (numeral p) (prod_pairs (toTerm ps))) :=
      eq_congr_mul_right (u := prod_pairs (toTerm ps)) h_pow
    have c3 : axioms ⊢ (mul (numeral p) (prod_pairs (toTerm ps)) =eq
                        mul (numeral p) (numeral (natProd ps))) :=
      eq_congr_mul_left (u := numeral p) ih
    have c4 : axioms ⊢ (mul (numeral p) (numeral (natProd ps)) =eq
                        numeral (p * natProd ps)) :=
      numeral_mul p (natProd ps)
    exact FOL.derive_eq_trans (FOL.derive_eq_trans (FOL.derive_eq_trans c1 c2) c3) c4

/-- **TFA — existencia (sobre numerales)**: todo `n ≥ 1` tiene una factorización
    prima object. `ps` es la lista meta de primos (lleva la primalidad vía
    `IsPrimeNat`); su encoding `toTerm ps` cumple `prod_pairs = numeral n`. -/
theorem tfa_exists_numeral (n : Nat) (hn : 1 ≤ n) :
    ∃ ps : List Nat, And (∀ p ∈ ps, IsPrimeNat p)
      (axioms ⊢ (prod_pairs (toTerm ps) =eq numeral n)) := by
  obtain ⟨ps, hprime, hprod⟩ := primeFactorList n hn
  refine ⟨ps, hprime, ?_⟩
  have h := prod_pairs_toTerm ps
  rw [hprod] at h
  exact h

/-- **TFA — existencia ∧ unicidad (sobre numerales)**. Para todo `n ≥ 1`:
    existe una factorización prima `ps` cuyo encoding object cumple
    `prod_pairs (toTerm ps) = numeral n` (**existencia**, object), y toda
    factorización prima de `n` es una permutación de `ps` (**unicidad**, ℕ).

    Es la realización constructiva del TFA sobre numerales. La unicidad se
    enuncia con la hipótesis meta `natProd qs = n` (no object): así no requiere
    reflejar igualdad de numerales (que necesitaría `Con(axioms)`). El
    `ax_p_tfa` de `Block8` (meta-axioma con membership object y testigo único
    object) queda como la forma *idealizada* — no discharge constructivo por
    el Muro 1. -/
theorem tfa_numeral (n : Nat) (hn : 1 ≤ n) :
    ∃ ps : List Nat, And (∀ p ∈ ps, IsPrimeNat p)
      (And (axioms ⊢ (prod_pairs (toTerm ps) =eq numeral n))
           (∀ qs : List Nat, (∀ q ∈ qs, IsPrimeNat q) → natProd qs = n →
              ps.Perm qs)) := by
  obtain ⟨ps, hprime, hprod⟩ := primeFactorList n hn
  refine ⟨ps, hprime, ?_, ?_⟩
  · -- existencia object
    have h := prod_pairs_toTerm ps
    rw [hprod] at h
    exact h
  · -- unicidad (ℕ)
    intro qs hqs hqs_prod
    exact factorization_perm_unique ps qs hprime hqs (hprod.trans hqs_prod.symm)

end ROBINSON_PlusPlus.Full
