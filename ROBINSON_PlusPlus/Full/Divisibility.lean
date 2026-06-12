/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block8
import ROBINSON_PlusPlus.Full.Induction
import ROBINSON_PlusPlus.Full.StrongInduction
import ROBINSON_PlusPlus.Full.Numerals

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
## FULL — Divisibilidad representada

Dos piezas hacia la representabilidad de la primalidad:

* `numeral_dvd` : `a ∣ b` (meta) ⇒ `Dvd (numeral a) (numeral b)` (object).
  La divisibilidad meta se transfiere construyendo el cofactor numeral.

* `divisor_le` : `d · q = n ∧ n > 0` ⇒ `d ≤ n`. Un divisor de un positivo
  es `≤` él. Pieza para acotar los divisores candidatos (con `le_numeral_split`).
-/

/-! ### Helpers aritméticos object-level -/

private theorem add_zero_t (a : Term) : axioms ⊢ (add a zero =eq a) := by
  have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) a
  simp [substFormula, substTerm, substTerms, add, zero] at hh; exact hh

private theorem add_succ_t (a b : Term) : axioms ⊢ (add a (succ b) =eq succ (add a b)) := by
  have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) a) b
  simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh; exact hh

private theorem mul_zero_t (a : Term) : axioms ⊢ (mul a zero =eq zero) := by
  have hh := spec (ax (by simp [axioms] : ax8_mul_zero ∈ axioms)) a
  simp [substFormula, substTerm, substTerms, mul, zero] at hh; exact hh

private theorem mul_succ_t (a b : Term) : axioms ⊢ (mul a (succ b) =eq add (mul a b) a) := by
  have hh := spec (spec (ax (by simp [axioms] : ax9_mul_succ ∈ axioms)) a) b
  simp [substFormula, substTerm, substTerms, mul, add, succ, FOL.substTerm_liftTerm] at hh; exact hh

private theorem add_comm_t (a b : Term) : axioms ⊢ (add a b =eq add b a) := by
  have hh := spec (add_comm_ax a) b
  simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftTerm] at hh; exact hh

/-- Construcción de `lt` desde testigo: `a + σk = b → lt a b`. -/
private theorem lt_intro_t (a b k : Term) (h : axioms ⊢ (add a (succ k) =eq b)) :
    axioms ⊢ lt a b := by
  have h13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have hiff := spec (spec h13 a) b
  simp [substFormula, substTerm, substTerms, lt, succ, iff, liftTerm, liftTerms,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hiff
  apply iff_mpr hiff
  apply ex_intro k
  simp [substFormula, substTerm, substTerms, add, succ,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift]
  exact h

/-! ### `numeral_dvd`: divisibilidad meta ⇒ object -/

/-- `a ∣ b` (meta) ⇒ `Dvd (numeral a) (numeral b)`. Cofactor: `numeral (b/a)`. -/
theorem numeral_dvd {a b : Nat} (h : a ∣ b) : Dvd (numeral a) (numeral b) := by
  obtain ⟨c, hc⟩ := h        -- b = a * c
  refine ⟨numeral c, ?_⟩
  -- axioms ⊢ mul (numeral a) (numeral c) =eq numeral b
  have hhom : axioms ⊢ (mul (numeral a) (numeral c) =eq numeral (a * c)) := numeral_mul a c
  rw [hc]                     -- b = a * c (defeq de numeral)
  exact hhom

/-! ### `divisor_le`: un divisor de un positivo es `≤` él -/

/-- `d · q = n ∧ n > 0 ⇒ d ≤ n`.

    `q ≠ 0` (sino `n = 0`), así `q = σq'` y `n = d·q' + d = d + d·q'`.
    Si `d·q' = 0` entonces `n = d`; si `d·q' = σm` entonces `d < n`. -/
theorem divisor_le (d q n : Term)
    (hq : axioms ⊢ (mul d q =eq n)) (hn : axioms ⊢ lt zero n) :
    axioms ⊢ le d n := by
  -- q = 0 ∨ ∃q', q = σq'
  have hzos_q := spec zero_or_succ_ax q
  simp [substFormula, substTerm, substTerms, zero, succ,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hzos_q
  apply Minimal.Axioms.or_elim hzos_q
  · -- q = 0 → d·0 = 0 = n → ⊥ (n > 0)
    intro hq0
    apply false_elim
    have hn0 : axioms ⊢ (n =eq zero) := by
      -- n = d·q = d·0 = 0
      have h1 : axioms ⊢ (mul d q =eq mul d zero) := eq_congr_mul_left (u := d) hq0
      have h2 : axioms ⊢ (mul d zero =eq zero) := mul_zero_t d
      exact eq_trans hq (FOL.derive_eq_trans h1 h2)
    -- lt zero n con n = 0 → lt zero zero → ⊥ (ax18)
    have hlt00 : axioms ⊢ lt zero zero := by
      let f : Formula := lt zero (.var 0)
      have hS : ∀ s : Term, substFormula 0 s f = lt zero s := by
        intro s; simp [f, substFormula, lt, substTerm, substTerms, zero, FOL.substTerm_liftTerm]
      exact (hS zero) ▸ Derives.subst axioms n zero f hn0 ((hS n) ▸ hn)
    have hirr : axioms ⊢ neg (lt zero zero) := by
      have hh := spec lt_irrefl_thm zero
      simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at hh
      exact hh
    exact mp hirr hlt00
  · -- ∃q', q = σq'
    intro hex
    apply ex_elim hex; intro q' hq'
    simp [substFormula, substTerm, substTerms, succ,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hq'
    -- hq' : q =eq σq'.  n = d·q = d·σq' = d·q' + d
    have hn_eq : axioms ⊢ (n =eq add (mul d q') d) := by
      have h1 : axioms ⊢ (mul d q =eq mul d (succ q')) := eq_congr_mul_left (u := d) hq'
      have h2 : axioms ⊢ (mul d (succ q') =eq add (mul d q') d) := mul_succ_t d q'
      exact eq_trans hq (FOL.derive_eq_trans h1 h2)
    -- n = d + d·q'  (comm)
    have hn_eq2 : axioms ⊢ (n =eq add d (mul d q')) :=
      FOL.derive_eq_trans hn_eq (add_comm_t (mul d q') d)
    -- d·q' = 0 ∨ ∃m, d·q' = σm
    have hzos_m := spec zero_or_succ_ax (mul d q')
    simp [substFormula, substTerm, substTerms, zero, succ,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hzos_m
    apply Minimal.Axioms.or_elim hzos_m
    · -- d·q' = 0 → n = d + 0 = d → d = n
      intro hm0
      apply Minimal.Axioms.or_intro_right
      -- d =eq n.  d·q' = 0 ⇒ add d (d·q') = add d 0 = d; y n = add d (d·q')
      have h1 : axioms ⊢ (add d (mul d q') =eq add d zero) := eq_congr_add_left (u := d) hm0
      have h2 : axioms ⊢ (add d zero =eq d) := add_zero_t d
      have hnd : axioms ⊢ (n =eq d) :=
        FOL.derive_eq_trans hn_eq2 (FOL.derive_eq_trans h1 h2)
      exact eq_symm hnd
    · -- d·q' = σm → n = d + σm → d < n
      intro hexm
      apply ex_elim hexm; intro m hm
      simp [substFormula, substTerm, substTerms, succ,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hm
      -- hm : d·q' =eq σm.  n = d + σm
      apply Minimal.Axioms.or_intro_left
      have hn_dm : axioms ⊢ (add d (succ m) =eq n) := by
        -- n =eq add d (d·q') =eq add d (σm); invertir
        have h1 : axioms ⊢ (add d (mul d q') =eq add d (succ m)) := eq_congr_add_left (u := d) hm
        exact eq_symm (FOL.derive_eq_trans hn_eq2 h1)
      exact lt_intro_t d n m hn_dm

end ROBINSON_PlusPlus.Full
