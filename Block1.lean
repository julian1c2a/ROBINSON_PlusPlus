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


/-!
### Fase 2: Identidades del 0 y del 1
-/

-- Teo 2.1: ∀ n, n + 0 = n
-- Prueba: Ax 4.
theorem teo_2_1 : Γ ⊢ ax4_add_zero :=
  ax (by simp [axioms, ax4_add_zero])

-- Teo 2.2: ∀ n, 0 + n = n
-- Prueba: 0 + n = n + 0 (Ax 6) y n + 0 = n (Teo 2.1).
theorem teo_2_2 : Γ ⊢ forall_ (add zero (.var 0) =eq (.var 0)) := by
  apply gen
  have h_ax6 : Γ ⊢ ax6_add_comm := ax (by simp [axioms, ax6_add_comm])
  let h_spec_n := spec h_ax6 (t := zero)
  let h_comm := spec h_spec_n (t := .var 0)
  have h_ax4 : Γ ⊢ ax4_add_zero := ax (by simp [axioms, ax4_add_zero])
  let h_add_zero := spec h_ax4 (t := .var 0)
  exact eq_trans h_comm h_add_zero

-- Teo 2.3: ∀ n, n * 0 = 0
-- Prueba: Ax 8.
theorem teo_2_3 : Γ ⊢ ax8_mul_zero :=
  ax (by simp [axioms, ax8_mul_zero])

-- Teo 2.4: ∀ n, 0 * n = 0
-- Prueba: 0 * n = n * 0 (Ax 10) y n * 0 = 0 (Teo 2.3).
theorem teo_2_4 : Γ ⊢ forall_ (mul zero (.var 0) =eq zero) := by
  apply gen
  have h_ax10 : Γ ⊢ ax10_mul_comm := ax (by simp [axioms, ax10_mul_comm])
  let h_spec_n := spec h_ax10 (t := zero)
  let h_comm := spec h_spec_n (t := .var 0)
  have h_ax8 : Γ ⊢ ax8_mul_zero := ax (by simp [axioms, ax8_mul_zero])
  let h_mul_zero := spec h_ax8 (t := .var 0)
  exact eq_trans h_comm h_mul_zero

-- Teo 2.5: ∀ n, n * 1 = n
-- Prueba: n * 1 = n * σ(0) = (n * 0) + n = 0 + n = n por Ax 9, Ax 8, Teo 2.2.
theorem teo_2_5 : Γ ⊢ forall_ (mul (.var 0) one =eq (.var 0)) := by
  apply gen
  have h1 : Γ ⊢ mul (.var 0) one =eq mul (.var 0) (succ zero) := eq_refl
  have h_ax9 : Γ ⊢ ax9_mul_succ := ax (by simp [axioms, ax9_mul_succ])
  let h_spec_n := spec h_ax9 (t := .var 0)
  have h2 : Γ ⊢ mul (.var 0) (succ zero) =eq add (mul (.var 0) zero) (.var 0) :=
    spec h_spec_n (t := zero)
  have h_ax8 : Γ ⊢ ax8_mul_zero := ax (by simp [axioms, ax8_mul_zero])
  have h_mul_zero : Γ ⊢ mul (.var 0) zero =eq zero := spec h_ax8 (t := .var 0)
  have h3 : Γ ⊢ add (mul (.var 0) zero) (.var 0) =eq add zero (.var 0) :=
    eq_congr_add_left h_mul_zero
  have h_teo_2_2 : Γ ⊢ forall_ (add zero (.var 0) =eq (.var 0)) := teo_2_2
  have h4 : Γ ⊢ add zero (.var 0) =eq (.var 0) := spec h_teo_2_2 (t := .var 0)
  exact eq_trans h1 (eq_trans h2 (eq_trans h3 h4))

-- Teo 2.6: ∀ n, 1 * n = n
-- Prueba: 1 * n = n * 1 (Ax 10) y n * 1 = n (Teo 2.5).
theorem teo_2_6 : Γ ⊢ forall_ (mul one (.var 0) =eq (.var 0)) := by
  apply gen
  have h_ax10 : Γ ⊢ ax10_mul_comm := ax (by simp [axioms, ax10_mul_comm])
  let h_spec_n := spec h_ax10 (t := one)
  let h_comm := spec h_spec_n (t := .var 0)
  have h_teo_2_5 : Γ ⊢ forall_ (mul (.var 0) one =eq (.var 0)) := teo_2_5
  let h_mul_one := spec h_teo_2_5 (t := .var 0)
  exact eq_trans h_comm h_mul_one

-- Teo 2.7: ∀ n, 2 * n = n + n
-- Prueba: 2 * n = n * 2 = n * σ(1) = (n * 1) + n = n + n por Ax 10, Ax 9, Teo 2.5.
theorem teo_2_7 : Γ ⊢ forall_ (mul two (.var 0) =eq add (.var 0) (.var 0)) := by
  apply gen
  have h_ax10 : Γ ⊢ ax10_mul_comm := ax (by simp [axioms, ax10_mul_comm])
  let h_spec_n := spec h_ax10 (t := two)
  let h_comm := spec h_spec_n (t := .var 0)
  have h_n_mul_2_eq_n_mul_s1 : Γ ⊢ mul (.var 0) two =eq mul (.var 0) (succ one) := eq_refl
  have h_ax9 : Γ ⊢ ax9_mul_succ := ax (by simp [axioms, ax9_mul_succ])
  let h_spec_n_ax9 := spec h_ax9 (t := .var 0)
  let h_mul_succ := spec h_spec_n_ax9 (t := one)
  have h_teo_2_5 : Γ ⊢ forall_ (mul (.var 0) one =eq (.var 0)) := teo_2_5
  let h_mul_one_is_n := spec h_teo_2_5 (t := .var 0)
  have h_congr : Γ ⊢ add (mul (.var 0) one) (.var 0) =eq add (.var 0) (.var 0) := eq_congr_add_right h_mul_one_is_n
  exact eq_trans h_comm (eq_trans h_n_mul_2_eq_n_mul_s1 (eq_trans h_mul_succ h_congr))

-- Teo 2.8: ∀ n, σ(n) = n + 1
-- Prueba: n + 1 = n + σ(0) = σ(n + 0) = σ(n) por Ax 5, Ax 4.
theorem teo_2_8 : Γ ⊢ forall_ (succ (.var 0) =eq add (.var 0) one) := by
  apply gen
  have h1 : Γ ⊢ add (.var 0) one =eq add (.var 0) (succ zero) := eq_refl
  have h_ax5 : Γ ⊢ ax5_add_succ := ax (by simp [axioms, ax5_add_succ])
  let h_spec_n := spec h_ax5 (t := .var 0)
  let h2 := spec h_spec_n (t := zero)
  have h_ax4 : Γ ⊢ ax4_add_zero := ax (by simp [axioms, ax4_add_zero])
  let h_add_zero := spec h_ax4 (t := .var 0)
  have h3 := eq_congr_succ h_add_zero
  exact eq_symm (eq_trans h1 (eq_trans h2 h3))

-- Teo 3.11 (Predecessor Axiom as Theorem)
-- Needed for Teo 2.9 and 2.10. Its proof depends on order axioms.
theorem teo_3_11 : Γ ⊢ forall_ (neg ((.var 0) =eq zero) ⇒ ex (succ (.var 0) =eq (.var 1))) := by
  apply gen; intro n; apply imp_intro; intro h_n_neq_0
  have h_ax19 : Γ ⊢ ax19_lt_trichotomy := ax (by simp [axioms, ax19_lt_trichotomy])
  let h_spec_b := spec h_ax19 (t := n)
  let h_spec_a := spec h_spec_b (t := zero)
  apply or_elim h_spec_a
  · intro h_0_lt_n
    have h_ax13 : Γ ⊢ ax13_lt_def := ax (by simp [axioms, ax13_lt_def])
    let h_spec_m := spec h_ax13 (t := n)
    let h_spec_n := spec h_spec_m (t := zero)
    have h_exists_k : Γ ⊢ ex (add zero (succ (.var 0)) =eq n) := iff_mp h_spec_n h_0_lt_n
    apply ex_elim h_exists_k; intro k; intro h_0_add_sk_eq_n
    have h_teo_2_2_forall : Γ ⊢ forall_ (add zero (.var 0) =eq (.var 0)) := teo_2_2
    have h_0_add_sk_eq_sk : Γ ⊢ add zero (succ k) =eq succ k := spec h_teo_2_2_forall (t := succ k)
    have h_sk_eq_n : Γ ⊢ succ k =eq n := eq_trans (eq_symm h_0_add_sk_eq_sk) h_0_add_sk_eq_n
    exact ex_intro k h_sk_eq_n
  · intro h_0_eq_n
    have h_n_eq_0 : Γ ⊢ n =eq zero := eq_symm h_0_eq_n
    exact false_elim (h_n_neq_0 h_n_eq_0)
  · intro h_n_lt_0
    have h_ax13 : Γ ⊢ ax13_lt_def := ax (by simp [axioms, ax13_lt_def])
    let h_spec_m := spec h_ax13 (t := zero)
    let h_spec_n := spec h_spec_m (t := n)
    have h_exists_k : Γ ⊢ ex (add n (succ (.var 0)) =eq zero) := iff_mp h_spec_n h_n_lt_0
    apply ex_elim h_exists_k; intro k; intro h_n_add_sk_eq_0
    have h_ax5 : Γ ⊢ ax5_add_succ := ax (by simp [axioms, ax5_add_succ])
    let h_spec_m_ax5 := spec h_ax5 (t := k)
    let h_spec_n_ax5 := spec h_spec_m_ax5 (t := n)
    have h_n_add_sk_eq_s_nk : Γ ⊢ add n (succ k) =eq succ (add n k) := h_spec_n_ax5
    have h_s_nk_eq_0 : Γ ⊢ succ (add n k) =eq zero := eq_trans h_n_add_sk_eq_s_nk h_n_add_sk_eq_0
    have h_ax2 : Γ ⊢ ax2_peano_succ_neq_zero := ax (by simp [axioms, ax2_peano_succ_neq_zero])
    have h_s_nk_neq_0 : Γ ⊢ neg (succ (add n k) =eq zero) := spec h_ax2 (t := add n k)
    exact false_elim (h_s_nk_neq_0 h_s_nk_eq_0)

-- Teo 2.9: a + b = 0 ⇒ a = 0 ∧ b = 0
theorem teo_2_9 : Γ ⊢ forall_2 ( (add (.var 1) (.var 0) =eq zero) ⇒ (land ((.var 1) =eq zero) ((.var 0) =eq zero)) ) := by
  apply gen; intro a; apply gen; intro b; apply imp_intro; intro h_ab_eq_0
  have h_ax20 : Γ ⊢ ax20_eq_decidable := ax (by simp [axioms, ax20_eq_decidable])
  let h_spec_m := spec h_ax20 (t := zero)
  let h_dec_b := spec h_spec_m (t := b)
  apply or_elim h_dec_b
  · intro h_b_eq_0
    have h_a_add_0 : Γ ⊢ add a zero =eq zero := eq_trans (eq_congr_add_left h_b_eq_0) h_ab_eq_0
    have h_ax4 : Γ ⊢ ax4_add_zero := ax (by simp [axioms, ax4_add_zero])
    have h_a_add_0_eq_a : Γ ⊢ add a zero =eq a := spec h_ax4 (t := a)
    have h_a_eq_0 : Γ ⊢ a =eq zero := eq_trans (eq_symm h_a_add_0_eq_a) h_a_add_0
    exact and_intro h_a_eq_0 h_b_eq_0
  · intro h_b_neq_0
    have h_exists_m : Γ ⊢ ex (succ (.var 0) =eq b) := mp (spec teo_3_11 (t := b)) h_b_neq_0
    apply ex_elim h_exists_m; intro m; intro h_sm_eq_b
    have h_a_add_b_eq_a_add_sm : Γ ⊢ add a b =eq add a (succ m) := eq_congr_add_left h_sm_eq_b
    have h_ax5 : Γ ⊢ ax5_add_succ := ax (by simp [axioms, ax5_add_succ])
    let h_spec_m_ax5 := spec h_ax5 (t := m)
    let h_spec_n_ax5 := spec h_spec_m_ax5 (t := a)
    have h_a_add_sm_eq_s_am : Γ ⊢ add a (succ m) =eq succ (add a m) := h_spec_n_ax5
    have h_ab_eq_s_am : Γ ⊢ add a b =eq succ (add a m) := eq_trans h_a_add_b_eq_a_add_sm h_a_add_sm_eq_s_am
    have h_s_am_eq_0 : Γ ⊢ succ (add a m) =eq zero := eq_trans (eq_symm h_ab_eq_s_am) h_ab_eq_0
    have h_ax2 : Γ ⊢ ax2_peano_succ_neq_zero := ax (by simp [axioms, ax2_peano_succ_neq_zero])
    have h_s_am_neq_0 : Γ ⊢ neg (succ (add a m) =eq zero) := spec h_ax2 (t := add a m)
    exact false_elim (h_s_am_neq_0 h_s_am_eq_0)

-- Teo 2.10: a * b = 0 ⇒ a = 0 ∨ b = 0
theorem teo_2_10 : Γ ⊢ forall_2 ( (mul (.var 1) (.var 0) =eq zero) ⇒ (lor ((.var 1) =eq zero) ((.var 0) =eq zero)) ) := by
  apply gen; intro a; apply gen; intro b; apply imp_intro; intro h_ab_eq_0
  have h_ax20 : Γ ⊢ ax20_eq_decidable := ax (by simp [axioms, ax20_eq_decidable])
  let h_spec_m := spec h_ax20 (t := zero)
  let h_dec_b := spec h_spec_m (t := b)
  apply or_elim h_dec_b
  · intro h_b_eq_0
    exact or_intro_right h_b_eq_0
  · intro h_b_neq_0
    let h_dec_a := spec h_spec_m (t := a)
    apply or_elim h_dec_a
    · intro h_a_eq_0
      exact or_intro_left h_a_eq_0
    · intro h_a_neq_0
      have h_exists_k : Γ ⊢ ex (succ (.var 0) =eq b) := mp (spec teo_3_11 (t := b)) h_b_neq_0
      apply ex_elim h_exists_k; intro k; intro h_sk_eq_b
      have h_ab_eq_a_sk : Γ ⊢ mul a b =eq mul a (succ k) := eq_congr_mul_left h_sk_eq_b
      have h_ax9 : Γ ⊢ ax9_mul_succ := ax (by simp [axioms, ax9_mul_succ])
      let h_spec_m_ax9 := spec h_ax9 (t := k)
      let h_spec_n_ax9 := spec h_spec_m_ax9 (t := a)
      have h_a_sk_eq_ak_add_a : Γ ⊢ mul a (succ k) =eq add (mul a k) a := h_spec_n_ax9
      have h_ab_eq_ak_add_a : Γ ⊢ mul a b =eq add (mul a k) a := eq_trans h_ab_eq_a_sk h_a_sk_eq_ak_add_a
      have h_ak_add_a_eq_0 : Γ ⊢ add (mul a k) a =eq zero := eq_trans (eq_symm h_ab_eq_ak_add_a) h_ab_eq_0
      let h_spec_b_2_9 := spec teo_2_9 (t := a)
      let h_spec_a_2_9 := spec h_spec_b_2_9 (t := mul a k)
      have h_conj : Γ ⊢ land (mul a k =eq zero) (a =eq zero) := mp h_spec_a_2_9 h_ak_add_a_eq_0
      have h_a_eq_0_from_conj : Γ ⊢ a =eq zero := and_elim_right h_conj
      exact false_elim (h_a_neq_0 h_a_eq_0_from_conj)

-- Teo 2.11: 2 * a = 2 * b ⇒ a = b
theorem teo_2_11 : Γ ⊢ forall_2 ( (mul two (.var 1) =eq mul two (.var 0)) ⇒ ((.var 1) =eq (.var 0)) ) := by
  apply gen; intro a; apply gen; intro b; apply imp_intro; intro h_2a_eq_2b
  have h_mono_mul_2 : Γ ⊢ forall_2 ( (lt (.var 1) (.var 0)) ⇒ (lt (mul two (.var 1)) (mul two (.var 0))) ) := by
    apply gen; intro x; apply gen; intro y; apply imp_intro; intro h_x_lt_y
    have h_ax13 : Γ ⊢ ax13_lt_def := ax (by simp [axioms, ax13_lt_def])
    let h_spec_m_ax13 := spec h_ax13 (t := y)
    let h_spec_n_ax13 := spec h_spec_m_ax13 (t := x)
    have h_exists_k : Γ ⊢ ex (add x (succ (.var 0)) =eq y) := iff_mp h_spec_n_ax13 h_x_lt_y
    apply ex_elim h_exists_k; intro k; intro h_x_sk_eq_y
    have h_2y_eq_2_xsk : Γ ⊢ mul two y =eq mul two (add x (succ k)) := eq_congr_mul_left h_x_sk_eq_y
    have h_ax12 : Γ ⊢ ax12_mul_distrib := ax (by simp [axioms, ax12_mul_distrib])
    let h_spec_k_ax12 := spec h_ax12 (t := succ k)
    let h_spec_m_ax12 := spec h_spec_k_ax12 (t := x)
    let h_spec_n_ax12 := spec h_spec_m_ax12 (t := two)
    have h_distrib : Γ ⊢ mul two (add x (succ k)) =eq add (mul two x) (mul two (succ k)) := h_spec_n_ax12
    have h_2y_eq_2x_add_2sk : Γ ⊢ mul two y =eq add (mul two x) (mul two (succ k)) := eq_trans h_2y_eq_2_xsk h_distrib
    have h_teo_2_7_forall : Γ ⊢ forall_ (mul two (.var 0) =eq add (.var 0) (.var 0)) := teo_2_7
    have h_2sk_eq_sk_add_sk : Γ ⊢ mul two (succ k) =eq add (succ k) (succ k) := spec h_teo_2_7_forall (t := succ k)
    have h_ax5 : Γ ⊢ ax5_add_succ := ax (by simp [axioms, ax5_add_succ])
    let h_spec_m_ax5 := spec h_ax5 (t := k)
    let h_spec_n_ax5 := spec h_spec_m_ax5 (t := succ k)
    have h_sk_add_sk_eq_s_skk : Γ ⊢ add (succ k) (succ k) =eq succ (add (succ k) k) := h_spec_n_ax5
    let j := add (succ k) k
    have h_2sk_eq_sj : Γ ⊢ mul two (succ k) =eq succ j := eq_trans h_2sk_eq_sk_add_sk h_sk_add_sk_eq_s_skk
    have h_2y_eq_2x_add_sj : Γ ⊢ mul two y =eq add (mul two x) (succ j) := eq_trans h_2y_eq_2x_add_2sk (eq_congr_add_left h_2sk_eq_sj)
    let h_spec_m_ax13_2 := spec h_ax13 (t := mul two y)
    let h_spec_n_ax13_2 := spec h_spec_m_ax13_2 (t := mul two x)
    exact iff_mpr h_spec_n_ax13_2 (ex_intro j h_2y_eq_2x_add_sj)
  have h_ax19 : Γ ⊢ ax19_lt_trichotomy := ax (by simp [axioms, ax19_lt_trichotomy])
  let h_spec_b_ax19 := spec h_ax19 (t := b)
  let h_spec_a_ax19 := spec h_spec_b_ax19 (t := a)
  apply or_elim h_spec_a_ax19
  · intro h_a_lt_b
    let h_spec_b_mono := spec h_mono_mul_2 (t := b)
    let h_spec_a_mono := spec h_spec_b_mono (t := a)
    have h_2a_lt_2b : Γ ⊢ lt (mul two a) (mul two b) := mp h_spec_a_mono h_a_lt_b
    have h_2a_neq_2b : Γ ⊢ neg (mul two a =eq mul two b) := by
      apply raa; intro h_2a_eq_2b_hyp
      have h_2a_lt_2a : Γ ⊢ lt (mul two a) (mul two a) := eq_subst h_2a_eq_2b_hyp h_2a_lt_2b
      have h_ax18 : Γ ⊢ ax18_lt_irrefl := ax (by simp [axioms, ax18_lt_irrefl])
      have h_irr := spec h_ax18 (t := mul two a)
      exact h_irr h_2a_lt_2a
    exact false_elim (h_2a_neq_2b h_2a_eq_2b)
  · intro h_a_eq_b
    exact h_a_eq_b
  · intro h_b_lt_a
    let h_spec_b_mono := spec h_mono_mul_2 (t := a)
    let h_spec_a_mono := spec h_spec_b_mono (t := b)
    have h_2b_lt_2a : Γ ⊢ lt (mul two b) (mul two a) := mp h_spec_a_mono h_b_lt_a
    have h_2b_neq_2a : Γ ⊢ neg (mul two b =eq mul two a) := by
      apply raa; intro h_2b_eq_2a_hyp
      have h_2b_lt_2b : Γ ⊢ lt (mul two b) (mul two b) := eq_subst h_2b_eq_2a_hyp h_2b_lt_2a
      have h_ax18 : Γ ⊢ ax18_lt_irrefl := ax (by simp [axioms, ax18_lt_irrefl])
      have h_irr := spec h_ax18 (t := mul two b)
      exact h_irr h_2b_lt_2b
    have h_2a_neq_2b : Γ ⊢ neg (mul two a =eq mul two b) := eq_symm_neg h_2b_neq_2a
    exact false_elim (h_2a_neq_2b h_2a_eq_2b)

end ROBINSON_PlusPlus.Minimal.Theorems.Block1
