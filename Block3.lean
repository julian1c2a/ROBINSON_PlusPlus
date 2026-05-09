/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block2

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Metamath.Deduction

open FOL.FOL
open FOL.Tactics
open FOL.Theorems
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1
-- Block2 is not strictly needed for the first theorems, but will be for later ones.
-- open ROBINSON_PlusPlus.Minimal.Theorems.Block2

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block3

/-!
## BLOQUE III — div2 Y mod2
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 5: Valores de div2 y mod2 como Teoremas
-/

-- Teo 5.1: mod2(0) = 0
theorem mod2_zero : Γ ⊢ mod2 zero =eq zero := by
  -- From Ax 17: (div2(0) * 2) + mod2(0) = 0
  have h_ax17_spec := spec (ax (by simp [axioms, ax17_div_mod_eq])) (t := zero)
  -- From Teo 2.9: a + b = 0 ⇒ a = 0 ∧ b = 0
  let h_teo2_9_spec := spec (spec teo_2_9 (t := mod2 zero)) (t := mul (div2 zero) two)
  have h_conj : Γ ⊢ land (mul (div2 zero) two =eq zero) (mod2 zero =eq zero) := mp h_teo2_9_spec h_ax17_spec
  exact and_elim_right h_conj

-- Teo 5.2: div2(0) = 0
theorem div2_zero : Γ ⊢ div2 zero =eq zero := by
  -- From Ax 17: (div2(0) * 2) + mod2(0) = 0
  have h_ax17_spec := spec (ax (by simp [axioms, ax17_div_mod_eq])) (t := zero)
  -- From Teo 2.9: a + b = 0 ⇒ a = 0 ∧ b = 0
  let h_teo2_9_spec := spec (spec teo_2_9 (t := mod2 zero)) (t := mul (div2 zero) two)
  have h_conj : Γ ⊢ land (mul (div2 zero) two =eq zero) (mod2 zero =eq zero) := mp h_teo2_9_spec h_ax17_spec
  have h_mul_eq_zero : Γ ⊢ mul (div2 zero) two =eq zero := and_elim_left h_conj
  -- From Teo 2.10: a * b = 0 ⇒ a = 0 ∨ b = 0
  let h_teo2_10_spec := spec (spec teo_2_10 (t := two)) (t := div2 zero)
  have h_disj : Γ ⊢ lor (div2 zero =eq zero) (two =eq zero) := mp h_teo2_10_spec h_mul_eq_zero
  -- We know 2 ≠ 0 (from Teo 1.13_1, which is zero ≠ two)
  have h_two_neq_zero : Γ ⊢ neg (two =eq zero) := eq_symm_neg teo_1_13_1
  -- So we can conclude div2(0) = 0
  apply or_elim h_disj
  · intro h_div2_eq_zero
    exact h_div2_eq_zero
  · intro h_two_eq_zero
    exact false_elim (h_two_neq_zero h_two_eq_zero)

-- Teo 5.3: mod2(1) = 1
theorem mod2_one : Γ ⊢ mod2 one =eq one := by
  -- From Ax 16: mod2(n) = 0 ⇔ mod2(σ(n)) = 1
  have h_ax16_spec := spec (ax (by simp [axioms, ax16_mod2_succ])) (t := zero)
  -- We have mod2(0) = 0 from Teo 5.1, so by iff we get mod2(σ(0)) = 1.
  exact iff_mp h_ax16_spec mod2_zero

-- Teo 5.4: div2(1) = 0
theorem div2_one : Γ ⊢ div2 one =eq zero := by
  -- From Ax 17: (div2(1) * 2) + mod2(1) = 1
  have h_ax17_spec := spec (ax (by simp [axioms, ax17_div_mod_eq])) (t := one)
  -- Substitute mod2(1) = 1 (Teo 5.3)
  have h_step1 : Γ ⊢ add (mul (div2 one) two) one =eq one :=
    eq_trans (eq_congr_add_left mod2_one) h_ax17_spec
  -- From Teo 2.8, n + 1 = σ(n). So the LHS is σ(div2(1) * 2)
  have h_lhs_eq_succ : Γ ⊢ add (mul (div2 one) two) one =eq succ (mul (div2 one) two) :=
    eq_symm (spec teo_2_8 (t := mul (div2 one) two))
  -- The equation becomes σ(div2(1) * 2) = 1 = σ(0)
  have h_succ_eq_one : Γ ⊢ succ (mul (div2 one) two) =eq one := eq_trans (eq_symm h_lhs_eq_succ) h_step1
  -- By injectivity of σ (Ax 3), div2(1) * 2 = 0
  have h_mul_eq_zero : Γ ⊢ mul (div2 one) two =eq zero :=
    mp (spec (spec (ax ax3_peano_succ_inj) (t := zero)) (t := mul (div2 one) two)) h_succ_eq_one
  -- By Teo 2.10, div2(1) = 0 ∨ 2 = 0. Since 2 ≠ 0, we conclude div2(1) = 0.
  let h_teo2_10_spec := spec (spec teo_2_10 (t := two)) (t := div2 one)
  have h_disj : Γ ⊢ lor (div2 one =eq zero) (two =eq zero) := mp h_teo2_10_spec h_mul_eq_zero
  have h_two_neq_zero : Γ ⊢ neg (two =eq zero) := eq_symm_neg teo_1_13_1
  apply or_elim h_disj
  · intro h_div2_eq_zero; exact h_div2_eq_zero
  · intro h_two_eq_zero; exact false_elim (h_two_neq_zero h_two_eq_zero)

-- Teo 5.7: mod2(3) = 1
theorem mod2_three : Γ ⊢ mod2 three =eq one := by
  -- From Ax 16: mod2(n) = 0 ⇔ mod2(σ(n)) = 1. With n=2: mod2(2)=0 ⇔ mod2(3)=1
  have h_ax16_spec := spec (ax (by simp [axioms, ax16_mod2_succ])) (t := two)
  -- We have mod2(2) = 0 from Teo 5.5, so by iff we get mod2(3) = 1.
  exact iff_mp h_ax16_spec mod2_two

-- Teo 5.8: div2(3) = 1
theorem div2_three : Γ ⊢ div2 three =eq one := by
  -- From Ax 17: (div2(3) * 2) + mod2(3) = 3
  have h_ax17_spec := spec (ax (by simp [axioms, ax17_div_mod_eq])) (t := three)
  -- Substitute mod2(3) = 1 (Teo 5.7)
  have h_step1 : Γ ⊢ add (mul (div2 three) two) one =eq three :=
    eq_trans (eq_congr_add_left mod2_three) h_ax17_spec
  -- From Teo 2.8, n + 1 = σ(n). So the LHS is σ(div2(3) * 2)
  have h_lhs_eq_succ : Γ ⊢ add (mul (div2 three) two) one =eq succ (mul (div2 three) two) :=
    eq_symm (spec teo_2_8 (t := mul (div2 three) two))
  -- The equation becomes σ(div2(3) * 2) = 3 = σ(2)
  have h_succ_eq_three : Γ ⊢ succ (mul (div2 three) two) =eq three := eq_trans (eq_symm h_lhs_eq_succ) h_step1
  -- By injectivity of σ (Ax 3), div2(3) * 2 = 2
  have h_mul_eq_two : Γ ⊢ mul (div2 three) two =eq two :=
    mp (spec (spec (ax ax3_peano_succ_inj) (t := two)) (t := mul (div2 three) two)) h_succ_eq_three
  -- We have 2 * 1 = 2 (Teo 1.9)
  -- By commutativity on the LHS: 2 * div2(3) = 2
  have h_comm_lhs := spec (spec (ax ax10_mul_comm) (t := two)) (t := div2 three)
  have h_lhs_comm : Γ ⊢ mul two (div2 three) =eq two := eq_trans h_comm_lhs h_mul_eq_two
  -- So we have 2 * div2(3) = 2 * 1
  have h_eq_muls : Γ ⊢ mul two (div2 three) =eq mul two one := eq_trans h_lhs_comm (eq_symm teo_1_9)
  -- By Teo 2.11 (cancellation), div2(3) = 1
  exact mp (spec (spec teo_2_11 (t := one)) (t := div2 three)) h_eq_muls

-- Teo 5.9: mod2(4) = 0
theorem mod2_four : Γ ⊢ mod2 four =eq zero := by
  -- From Ax 16: mod2(n) = 0 ⇔ mod2(σ(n)) = 1. With n=3: mod2(3)=0 ⇔ mod2(4)=1
  have h_ax16_spec := spec (ax (by simp [axioms, ax16_mod2_succ])) (t := three)
  -- We know mod2(3) = 1 (Teo 5.7). So the LHS of the iff, mod2(3)=0, is false.
  have h_mod2_three_neq_zero : Γ ⊢ neg (mod2 three =eq zero) := by
    apply raa; intro h_mod2_three_eq_zero
    have h_one_eq_zero : Γ ⊢ one =eq zero := eq_trans (eq_symm mod2_three) h_mod2_three_eq_zero
    exact teo_1_11 (eq_symm h_one_eq_zero)
  -- Therefore, the RHS must be false: ¬(mod2(4) = 1)
  have h_mod2_four_neq_one : Γ ⊢ neg (mod2 four =eq one) := (iff_false_right h_ax16_spec) h_mod2_three_neq_zero
  -- From Ax 21: mod2(4) = 0 ∨ mod2(4) = 1
  have h_ax21_spec := spec (ax (by simp [axioms, ax21_mod2_range])) (t := four)
  -- By disjunctive syllogism, mod2(4) = 0
  apply or_elim h_ax21_spec
  · intro h_mod2_four_eq_zero
    exact h_mod2_four_eq_zero
  · intro h_mod2_four_eq_one
    exact false_elim (h_mod2_four_neq_one h_mod2_four_eq_one)

-- Teo 5.9: div2(4) = 2
theorem div2_four : Γ ⊢ div2 four =eq two := by
  -- From Ax 17: (div2(4) * 2) + mod2(4) = 4
  have h_ax17_spec := spec (ax (by simp [axioms, ax17_div_mod_eq])) (t := four)
  -- Substitute mod2(4) = 0 (Teo 5.9)
  have h_step1 : Γ ⊢ add (mul (div2 four) two) zero =eq four :=
    eq_trans (eq_congr_add_left mod2_four) h_ax17_spec
  -- From Ax 4, n + 0 = n. So LHS is div2(4) * 2
  have h_lhs_eq_mul : Γ ⊢ add (mul (div2 four) two) zero =eq mul (div2 four) two :=
    spec (ax ax4_add_zero) (t := mul (div2 four) two)
  -- So, div2(4) * 2 = 4
  have h_mul_eq_four : Γ ⊢ mul (div2 four) two =eq four := eq_trans (eq_symm h_lhs_eq_mul) h_step1
  -- We know 2 * 2 = 4 (Teo 1.10)
  -- By commutativity on the LHS: 2 * div2(4) = 4
  have h_comm_lhs := spec (spec (ax ax10_mul_comm) (t := two)) (t := div2 four)
  have h_lhs_comm : Γ ⊢ mul two (div2 four) =eq four := eq_trans h_comm_lhs h_mul_eq_four
  -- So we have 2 * div2(4) = 2 * 2
  have h_eq_muls : Γ ⊢ mul two (div2 four) =eq mul two two := eq_trans h_lhs_comm (eq_symm teo_1_10)
  -- By Teo 2.11 (cancellation), div2(4) = 2
  exact mp (spec (spec teo_2_11 (t := two)) (t := div2 four)) h_eq_muls

-- Teo 5.10: ∀ n, mod2(n) = 0 ∨ mod2(n) = 1
theorem mod2_range : Γ ⊢ ax21_mod2_range :=
  ax (by simp [axioms, ax21_mod2_range])

end ROBINSON_PlusPlus.Minimal.Theorems.Block3

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block3 (
  mod2_zero
  div2_zero
  mod2_one
  div2_one
  mod2_two
  div2_two
  mod2_three
  div2_three
  mod2_four
  div2_four
  mod2_range
)
