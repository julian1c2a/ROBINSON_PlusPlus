/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block8
import ROBINSON_PlusPlus.Full.Induction
import ROBINSON_PlusPlus.Full.Numerals
import ROBINSON_PlusPlus.Full.Bounded
import ROBINSON_PlusPlus.Full.Divisibility

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1
open ROBINSON_PlusPlus.Minimal.Theorems.Block8

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Full

/-!
## FULL — Primalidad representada

`isPrime_numeral` : si `p` es primo (hipótesis meta sobre `ℕ`, sin Mathlib:
`2 ≤ p` y todo divisor de `p` es `1` o `p`), entonces `IsPrime (numeral p)`
(la primalidad object de Block8).

La segunda condición de `IsPrime` (`∀ d, Dvd d (numeral p) → d=1 ∨ d=numeral p`)
se prueba: el divisor `d` cumple `d ≤ numeral p` (`divisor_le`), luego
`le_numeral_split` reduce a casos finitos `d = numeral i` (`i ≤ p`); en cada
caso se decide a nivel meta:
* `i = 0`: `d·q = numeral p = 0` contradice `p ≠ 0`.
* `i = 1`, `i = p`: dan directamente la disyunción.
* `1 < i < p`: `i ∤ p` (primalidad), y un **split anidado** sobre el cofactor
  `q` da `numeral (i·j) = numeral p` con `i·j ≠ p` — contradicción.
-/

/-! ### Helpers -/

private theorem zero_mul_t (a : Term) : axioms ⊢ (mul zero a =eq zero) := by
  have hh := spec zero_mul a
  simp [substFormula, substTerm, substTerms, mul, zero] at hh; exact hh

private theorem mul_comm_t (a b : Term) : axioms ⊢ (mul a b =eq mul b a) := by
  have hh := spec (mul_comm_ax a) b
  simp [substFormula, substTerm, substTerms, mul, FOL.substTerm_liftTerm] at hh; exact hh

/-! ### Primalidad representada -/

/-- `p` primo (meta) ⇒ `IsPrime (numeral p)`.

    Primalidad como hipótesis meta sin Mathlib: `2 ≤ p` y todo divisor de `p`
    (en `ℕ`) es `1` o `p`. -/
theorem isPrime_numeral (p : Nat) (hp2 : Nat.le 2 p)
    (hpd : ∀ a : Nat, a ∣ p → Or (a = 1) (a = p)) :
    IsPrime (numeral p) := by
  -- cotas meta derivadas de hp2 (omega no lee la forma cruda `Nat.le 2 p`)
  have h0p : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  have h1p : 1 < p := Nat.lt_of_lt_of_le (by decide) hp2
  refine ⟨?_, ?_⟩
  · -- lt one (numeral p) : numeral 1 = one defeq
    exact numeral_lt (a := 1) (b := p) h1p
  · intro d hd_dvd
    obtain ⟨q, hq⟩ := hd_dvd
    -- hq : axioms ⊢ mul d q =eq numeral p
    have hle : axioms ⊢ le d (numeral p) :=
      divisor_le d q (numeral p) hq (numeral_lt (a := 0) (b := p) h0p)
    refine le_numeral_split d ((d =eq one) ∨ (d =eq numeral p)) p hle ?_
    intro i hi heqi
    by_cases hi1 : i = 1
    · rw [hi1] at heqi
      exact Minimal.Axioms.or_intro_left heqi   -- numeral 1 = one defeq
    by_cases hip : i = p
    · rw [hip] at heqi
      exact Minimal.Axioms.or_intro_right heqi
    by_cases hi0 : i = 0
    · -- d = 0 → d·q = 0 = numeral p, contradice p ≠ 0
      subst hi0
      apply false_elim
      have h_dz : axioms ⊢ (d =eq zero) := heqi
      have h_dq_z : axioms ⊢ (mul d q =eq zero) :=
        FOL.derive_eq_trans (eq_congr_mul_right (u := q) h_dz) (zero_mul_t q)
      have hp_zero : axioms ⊢ (numeral p =eq zero) := eq_trans hq h_dq_z
      exact mp (numeral_ne (by omega : p ≠ 0)) hp_zero
    · -- 2 ≤ i < p, i ∤ p: split anidado sobre el cofactor q
      apply false_elim
      have hndvd : ¬ i ∣ p := fun hd => by rcases hpd i hd with h | h <;> omega
      have hq' : axioms ⊢ (mul (numeral i) q =eq numeral p) :=
        eq_trans (eq_congr_mul_right (u := q) heqi) hq
      have hqi : axioms ⊢ (mul q (numeral i) =eq numeral p) :=
        FOL.derive_eq_trans (mul_comm_t q (numeral i)) hq'
      have hle_q : axioms ⊢ le q (numeral p) :=
        divisor_le q (numeral i) (numeral p) hqi (numeral_lt (a := 0) (b := p) (by omega))
      refine le_numeral_split q Formula.bottom p hle_q ?_
      intro j hj heqj
      have hij : axioms ⊢ (mul (numeral i) (numeral j) =eq numeral p) :=
        eq_trans (eq_congr_mul_left (u := numeral i) heqj) hq'
      have hp_eq : axioms ⊢ (numeral (i * j) =eq numeral p) :=
        eq_trans (numeral_mul i j) hij
      have hne : i * j ≠ p := fun he => hndvd ⟨j, he.symm⟩
      exact mp (numeral_ne hne) hp_eq

end ROBINSON_PlusPlus.Full
