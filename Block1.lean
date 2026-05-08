/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import FOL.FOL
import FOL.Tactics

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block1

open ROBINSON_PlusPlus.Minimal.Axioms
open FOL.Formula
open FOL.Derives

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

-- Local definitions from TuplasFuncionesYListas.md Def 3-4
def three : Term := succ two
def four : Term := succ three

/-!
## BLOQUE I — ARITMÉTICA BÁSICA
### Fase 1: Evaluación de Constantes
-/

-- Teo 1.1: 1 + 0 = 1
-- Prueba: Ax 4 (∀ n, n + 0 = n) con n := 1.
theorem teo_1_1 : Γ ⊢ add one zero =eq one := by
  have h_ax4 : Γ ⊢ ax4_add_zero := ax (by simp [axioms, ax4_add_zero])
  exact spec h_ax4 (t := one)

-- Teo 1.2: 0 + 1 = 1
-- Prueba: 0 + 1 = 1 + 0 (Ax 6) y 1 + 0 = 1 (Teo 1.1).
theorem teo_1_2 : Γ ⊢ add zero one =eq one := by
  have h_ax6 : Γ ⊢ ax6_add_comm := ax (by simp [axioms, ax6_add_comm])
  let h_spec_m := spec h_ax6 (t := one)
  let h_spec_n := spec h_spec_m (t := zero)
  exact eq_trans h_spec_n teo_1_1

-- Teo 1.3: 1 + 1 = 2
-- Prueba: 1 + 1 = 1 + σ(0) = σ(1 + 0) = σ(1) = 2
theorem teo_1_3 : Γ ⊢ add one one =eq two := by
  -- 1. ⊢ 1 + 1 = 1 + σ(0)
  -- This is definitional since one := succ zero.
  have h1 : Γ ⊢ add one one =eq add one (succ zero) := eq_refl

  -- 2. ⊢ 1 + σ(0) = σ(1 + 0)
  -- From Ax 5 (∀n,∀m, n + σ(m) = σ(n+m)) with n:=1, m:=0
  have h_ax5 : Γ ⊢ ax5_add_succ := ax (by simp [axioms, ax5_add_succ])
  let h_spec_m := spec h_ax5 (t := zero)
  let h_spec_n := spec h_spec_m (t := one)
  have h2 := h_spec_n

  -- 3. ⊢ σ(1 + 0) = σ(1)
  -- From Teo 1.1 (1 + 0 = 1) by congruence.
  have h3 : Γ ⊢ succ (add one zero) =eq succ one := eq_congr_succ teo_1_1

  -- 4. ⊢ σ(1) = 2
  -- This is definitional since two := succ one.
  have h4 : Γ ⊢ succ one =eq two := eq_refl

  -- Chain them with transitivity
  exact eq_trans h1 (eq_trans h2 (eq_trans h3 h4))

-- Teo 1.4: 2 + 1 = 3
-- Prueba: 2 + 1 = 2 + σ(0) = σ(2 + 0) = σ(2) = 3
theorem teo_1_4 : Γ ⊢ add two one =eq three := by
  -- 1. ⊢ 2 + 1 = 2 + σ(0)
  have h1 : Γ ⊢ add two one =eq add two (succ zero) := eq_refl

  -- 2. ⊢ 2 + σ(0) = σ(2 + 0)
  -- From Ax 5 with n:=2, m:=0
  have h_ax5 : Γ ⊢ ax5_add_succ := ax (by simp [axioms, ax5_add_succ])
  let h_spec_m := spec h_ax5 (t := zero)
  let h_spec_n := spec h_spec_m (t := two)
  have h2 := h_spec_n

  -- 3. ⊢ σ(2 + 0) = σ(2)
  -- From Ax 4 (∀n, n+0=n) with n:=2, by congruence.
  have h_ax4 : Γ ⊢ ax4_add_zero := ax (by simp [axioms, ax4_add_zero])
  have h_spec_n_ax4 : Γ ⊢ add two zero =eq two := spec h_ax4 (t := two)
  have h3 : Γ ⊢ succ (add two zero) =eq succ two := eq_congr_succ h_spec_n_ax4

  -- 4. ⊢ σ(2) = 3
  -- Definitional since three := succ two.
  have h4 : Γ ⊢ succ two =eq three := eq_refl

  -- Chain them
  exact eq_trans h1 (eq_trans h2 (eq_trans h3 h4))

-- Teo 1.5: 1 + 2 = 3
-- Prueba: 1 + 2 = 2 + 1 (Ax 6) y 2 + 1 = 3 (Teo 1.4).
theorem teo_1_5 : Γ ⊢ add one two =eq three := by
  -- 1. ⊢ 1 + 2 = 2 + 1
  -- From Ax 6 (∀n,∀m, n+m=m+n) with n:=1, m:=2
  have h_ax6 : Γ ⊢ ax6_add_comm := ax (by simp [axioms, ax6_add_comm])
  let h_spec_m := spec h_ax6 (t := two)
  let h_spec_n := spec h_spec_m (t := one)
  have h1 := h_spec_n

  -- 2. ⊢ 2 + 1 = 3
  have h2 := teo_1_4

  -- Chain them with transitivity
  exact eq_trans h1 h2

-- Teo 1.6: 3 + 1 = 4
-- Prueba: 3 + 1 = 3 + σ(0) = σ(3 + 0) = σ(3) = 4
theorem teo_1_6 : Γ ⊢ add three one =eq four := by
  have h1 : Γ ⊢ add three one =eq add three (succ zero) := eq_refl
  have h_ax5 : Γ ⊢ ax5_add_succ := ax (by simp [axioms, ax5_add_succ])
  let h_spec_m := spec h_ax5 (t := zero)
  let h_spec_n := spec h_spec_m (t := three)
  have h2 := h_spec_n
  have h_ax4 : Γ ⊢ ax4_add_zero := ax (by simp [axioms, ax4_add_zero])
  have h_spec_n_ax4 : Γ ⊢ add three zero =eq three := spec h_ax4 (t := three)
  have h3 : Γ ⊢ succ (add three zero) =eq succ three := eq_congr_succ h_spec_n_ax4
  have h4 : Γ ⊢ succ three =eq four := eq_refl
  exact eq_trans h1 (eq_trans h2 (eq_trans h3 h4))

-- Teo 1.7: 2 + 2 = 4
-- Prueba: 2 + 2 = 2 + σ(1) = σ(2 + 1) = σ(3) = 4
theorem teo_1_7 : Γ ⊢ add two two =eq four := by
  have h1 : Γ ⊢ add two two =eq add two (succ one) := eq_refl
  have h_ax5 : Γ ⊢ ax5_add_succ := ax (by simp [axioms, ax5_add_succ])
  let h_spec_m := spec h_ax5 (t := one)
  let h_spec_n := spec h_spec_m (t := two)
  have h2 := h_spec_n
  have h3 : Γ ⊢ succ (add two one) =eq succ three := eq_congr_succ teo_1_4
  have h4 : Γ ⊢ succ three =eq four := eq_refl
  exact eq_trans h1 (eq_trans h2 (eq_trans h3 h4))

-- Teo 1.8: 1 * 1 = 1
-- Prueba: 1 * 1 = 1 * σ(0) = (1 * 0) + 1 = 0 + 1 = 1
theorem teo_1_8 : Γ ⊢ mul one one =eq one := by
  have h1 : Γ ⊢ mul one one =eq mul one (succ zero) := eq_refl
  have h_ax9 : Γ ⊢ ax9_mul_succ := ax (by simp [axioms, ax9_mul_succ])
  let h_spec_m := spec h_ax9 (t := zero)
  let h_spec_n := spec h_spec_m (t := one)
  have h2 := h_spec_n
  have h_ax8 : Γ ⊢ ax8_mul_zero := ax (by simp [axioms, ax8_mul_zero])
  have h_spec_n_ax8 : Γ ⊢ mul one zero =eq zero := spec h_ax8 (t := one)
  have h3 : Γ ⊢ add (mul one zero) one =eq add zero one := eq_congr_add_left h_spec_n_ax8
  have h4 := teo_1_2
  exact eq_trans h1 (eq_trans h2 (eq_trans h3 h4))

-- Teo 1.9: 2 * 1 = 2
-- Prueba: 2 * 1 = 2 * σ(0) = (2 * 0) + 2 = 0 + 2 = 2
theorem teo_1_9 : Γ ⊢ mul two one =eq two := by
  have h1 : Γ ⊢ mul two one =eq mul two (succ zero) := eq_refl
  have h_ax9 : Γ ⊢ ax9_mul_succ := ax (by simp [axioms, ax9_mul_succ])
  let h_spec_m := spec h_ax9 (t := zero)
  let h_spec_n := spec h_spec_m (t := two)
  have h2 := h_spec_n
  have h_ax8 : Γ ⊢ ax8_mul_zero := ax (by simp [axioms, ax8_mul_zero])
  have h_spec_n_ax8 : Γ ⊢ mul two zero =eq zero := spec h_ax8 (t := two)
  have h3 : Γ ⊢ add (mul two zero) two =eq add zero two := eq_congr_add_left h_spec_n_ax8
  have h_ax6 : Γ ⊢ ax6_add_comm := ax (by simp [axioms, ax6_add_comm])
  let h_spec_m_ax6 := spec h_ax6 (t := zero)
  let h_spec_n_ax6 := spec h_spec_m_ax6 (t := two)
  have h4_comm : Γ ⊢ add zero two =eq add two zero := h_spec_n_ax6
  have h_ax4 : Γ ⊢ ax4_add_zero := ax (by simp [axioms, ax4_add_zero])
  have h_spec_n_ax4 : Γ ⊢ add two zero =eq two := spec h_ax4 (t := two)
  have h4 : Γ ⊢ add zero two =eq two := eq_trans h4_comm h_spec_n_ax4
  exact eq_trans h1 (eq_trans h2 (eq_trans h3 h4))

-- Teo 1.10: 2 * 2 = 4
-- Prueba: 2 * 2 = 2 * σ(1) = (2 * 1) + 2 = 2 + 2 = 4
theorem teo_1_10 : Γ ⊢ mul two two =eq four := by
  have h1 : Γ ⊢ mul two two =eq mul two (succ one) := eq_refl
  have h_ax9 : Γ ⊢ ax9_mul_succ := ax (by simp [axioms, ax9_mul_succ])
  let h_spec_m := spec h_ax9 (t := one)
  let h_spec_n := spec h_spec_m (t := two)
  have h2 := h_spec_n
  have h3 : Γ ⊢ add (mul two one) two =eq add two two := eq_congr_add_left teo_1_9
  have h4 := teo_1_7
  exact eq_trans h1 (eq_trans h2 (eq_trans h3 h4))

-- Teo 1.11: 0 ≠ 1
-- Prueba: Ax 2 con n := 0: σ(0) ≠ 0, es decir 1 ≠ 0.
theorem teo_1_11 : Γ ⊢ neg (zero =eq one) := by
  apply raa; intro h_hyp
  have h_one_eq_zero : Γ ⊢ one =eq zero := eq_symm h_hyp
  have h_ax2 : Γ ⊢ ax2_peano_succ_neq_zero := ax (by simp [axioms, ax2_peano_succ_neq_zero])
  have h_spec : Γ ⊢ neg (succ zero =eq zero) := spec h_ax2 (t := zero)
  exact h_spec h_one_eq_zero

-- Teo 1.12: 1 ≠ 2
-- Prueba: Si 1 = 2 (σ(0) = σ(1)), por Ax 3: 0 = 1, contradiciendo Teo 1.11.
theorem teo_1_12 : Γ ⊢ neg (one =eq two) := by
  apply raa; intro h_hyp
  have h_s0_eq_s1 : Γ ⊢ succ zero =eq succ one := by simp [one, two] at h_hyp; exact h_hyp
  have h_ax3 : Γ ⊢ ax3_peano_succ_inj := ax (by simp [axioms, ax3_peano_succ_inj])
  let h_spec_m := spec h_ax3 (t := one)
  let h_spec_n := spec h_spec_m (t := zero)
  have h_zero_eq_one : Γ ⊢ zero =eq one := mp h_spec_n h_s0_eq_s1
  exact teo_1_11 h_zero_eq_one

-- Teo 1.13: Desigualdades entre constantes
theorem teo_1_13_1 : Γ ⊢ neg (zero =eq two) := by
  apply raa; intro h_hyp
  have h_ax2 : Γ ⊢ ax2_peano_succ_neq_zero := ax (by simp [axioms, ax2_peano_succ_neq_zero])
  have h_spec : Γ ⊢ neg (succ one =eq zero) := spec h_ax2 (t := one)
  exact h_spec (eq_symm h_hyp)

theorem teo_1_13_2 : Γ ⊢ neg (zero =eq three) := by
  apply raa; intro h_hyp
  have h_ax2 : Γ ⊢ ax2_peano_succ_neq_zero := ax (by simp [axioms, ax2_peano_succ_neq_zero])
  have h_spec : Γ ⊢ neg (succ two =eq zero) := spec h_ax2 (t := two)
  exact h_spec (eq_symm h_hyp)

theorem teo_1_13_3 : Γ ⊢ neg (one =eq three) := by
  apply raa; intro h_hyp
  have h_s0_eq_s2 : Γ ⊢ succ zero =eq succ two := by simp [one, three] at h_hyp; exact h_hyp
  have h_ax3 : Γ ⊢ ax3_peano_succ_inj := ax (by simp [axioms, ax3_peano_succ_inj])
  let h_spec_m := spec h_ax3 (t := two)
  let h_spec_n := spec h_spec_m (t := zero)
  have h_zero_eq_two : Γ ⊢ zero =eq two := mp h_spec_n h_s0_eq_s2
  exact teo_1_13_1 h_zero_eq_two

theorem teo_1_13_4 : Γ ⊢ neg (two =eq three) := by
  apply raa; intro h_hyp
  have h_s1_eq_s2 : Γ ⊢ succ one =eq succ two := by simp [two, three] at h_hyp; exact h_hyp
  have h_ax3 : Γ ⊢ ax3_peano_succ_inj := ax (by simp [axioms, ax3_peano_succ_inj])
  let h_spec_m := spec h_ax3 (t := two)
  let h_spec_n := spec h_spec_m (t := one)
  have h_one_eq_two : Γ ⊢ one =eq two := mp h_spec_n h_s1_eq_s2
  exact teo_1_12 h_one_eq_two

end ROBINSON_PlusPlus.Minimal.Theorems.Block1
