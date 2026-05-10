/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1

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

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block2

/-!
## BLOQUE II — RAÍZ CUADRADA
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 4: Cotas y Unicidad de √
-/

-- Teo 4.1: ∀ n, (√n)² ≤ n
theorem sqrt_sq_le (n : Term) : Γ ⊢ (sq (sqrt n)) ≤ n := by
  have h_ax14 : Γ ⊢ ax14_sqrt_le := ax (by simp [axioms, ax14_sqrt_le])
  exact spec h_ax14 (t := n)

-- Teo 4.2: ∀ n, n < (σ(√n))²
theorem lt_succ_sqrt_sq (n : Term) : Γ ⊢ n < (sq (succ (sqrt n))) := by
  have h_ax15 : Γ ⊢ ax15_lt_succ_sqrt := ax (by simp [axioms, ax15_lt_succ_sqrt])
  exact spec h_ax15 (t := n)

-- Teo 4.3: n² = 0 ⇒ n = 0
theorem sq_eq_zero_imp_zero (n : Term) : Γ ⊢ (sq n) = 0 ⇒ n = 0 := by
  apply deduction_theorem; intro h_sq_n_eq_0
  have h_n_mul_n_eq_0 : Γ ⊢ (mul n n) =eq 0 := by simp [sq] at h_sq_n_eq_0; exact h_sq_n_eq_0
  let h_teo_2_10_spec := spec (spec teo_2_10 (t := n)) (t := n)
  have h_n_eq_0_or_n_eq_0 : Γ ⊢ (n =eq zero) ∨ (n =eq zero) := mp h_teo_2_10_spec h_n_mul_n_eq_0
  -- From (A ∨ A) we can derive A
  apply or_elim h_n_eq_0_or_n_eq_0
  · intro h_n_eq_0_1
    exact h_n_eq_0_1
  · intro h_n_eq_0_2
    exact h_n_eq_0_2

-- Teorema (antes Ax 22): a < b ⇒ σ(a) ≤ b
theorem succ_le_of_lt {a b : Term} (h_lt : Γ ⊢ a < b) : Γ ⊢ (succ a) ≤ b := by
  -- Estrategia: Demostrar que `a < b` y `b < σ(a)` conduce a una contradicción.
  -- Por tricotomía, esto implica que si `a < b`, entonces `¬(b < σ(a))`,
  -- lo que nos deja con `σ(a) ≤ b`.

  have h_not_b_lt_sa : Γ ⊢ ¬(b < (succ a)) := by
    apply raa; intro h_b_lt_sa -- Asumimos `b < σ(a)` para llegar a una contradicción.

    -- Desempaquetamos las definiciones de `<` de las hipótesis.
    have h_ax13_ab := (iff_mp (spec (spec (ax13_lt_def (t₂ := a) (t₁ := b))))) h_lt
    have h_ax13_bsa := (iff_mp (spec (spec (ax13_lt_def (t₂ := b) (t₁ := succ a))))) h_b_lt_sa

    -- Eliminación existencial para obtener los testigos `k` y `j`.
    apply ex_elim h_ax13_ab; intro k; intro h_b_eq_a_sk
    apply ex_elim h_ax13_bsa; intro j; intro h_sa_eq_b_sj

    -- Sustituimos `b` en la segunda ecuación: `σ(a) = (a + σ(k)) + σ(j)`
    have h_sa_eq_ask_sj : Γ ⊢ (succ a) =eq add (add a (succ k)) (succ j) := by
      rwa [h_b_eq_a_sk] at h_sa_eq_b_sj

    -- Reagrupamos por asociatividad: `σ(a) = a + (σ(k) + σ(j))`
    have h_assoc : Γ ⊢ add (add a (succ k)) (succ j) =eq add a (add (succ k) (succ j)) :=
      spec (spec (spec (ax (by simp [axioms, ax7_add_assoc])) (t := succ j)) (t := succ k)) (t := a)
    have h_sa_eq_a_sksj : Γ ⊢ (succ a) =eq add a (add (succ k) (succ j)) := eq_trans h_sa_eq_ask_sj h_assoc

    -- Demostramos que `σ(k) + σ(j)` es siempre un sucesor.
    let p := add (succ k) (succ j)
    have h_p_is_succ : Γ ⊢ ex (succ (.var 0) =eq p) := by
      have h_p_eq_s_skj : Γ ⊢ p =eq succ (add (succ k) j) :=
        spec (spec (ax (by simp [axioms, ax5_add_succ])) (t := j)) (t := succ k)
      exact ex_intro (add (succ k) j) h_p_eq_s_skj

    -- La ecuación se convierte en `σ(a) = a + σ(q)` para algún `q`.
    apply ex_elim h_p_is_succ; intro q; intro h_p_eq_sq
    have h_sa_eq_a_sq : Γ ⊢ (succ a) =eq add a (succ q) := eq_trans h_sa_eq_a_sksj (eq_congr_add_left h_p_eq_sq)

    -- Usamos Ax 5 en el lado derecho: `a + σ(q) = σ(a+q)`.
    have h_a_sq_eq_s_aq : Γ ⊢ add a (succ q) =eq succ (add a q) :=
      spec (spec (ax (by simp [axioms, ax5_add_succ])) (t := q)) (t := a)
    have h_sa_eq_s_aq : Γ ⊢ (succ a) =eq succ (add a q) := eq_trans h_sa_eq_a_sq h_a_sq_eq_s_aq

    -- Por inyectividad de `σ` (Ax 3), obtenemos `a = a + q`.
    have h_a_eq_aq : Γ ⊢ a =eq add a q :=
      mp (spec (spec (ax (by simp [axioms, ax3_peano_succ_inj])) (t := add a q)) (t := a)) h_sa_eq_s_aq

    -- Demostramos que `q` también es siempre un sucesor.
    have h_q_is_succ : Γ ⊢ ex (succ (.var 0) =eq q) := by
      -- q = add (succ k) j
      have h_ax20 := ax (by simp [axioms, ax20_eq_decidable])
      apply or_elim (spec (spec h_ax20 (t := zero)) (t := j))
      · intro h_j_eq_0
        have h_q_eq_sk : Γ ⊢ q =eq succ k := by rw [h_j_eq_0]; exact spec (ax4_add_zero) (t := succ k)
        exact ex_intro k h_q_eq_sk
      · intro h_j_neq_0
        apply ex_elim (mp (spec exists_pred_of_ne_zero (t := j)) h_j_neq_0); intro j'; intro h_j_eq_sj'
        have h_q_eq_sk_sj' : Γ ⊢ q =eq add (succ k) (succ j') := by rw [h_j_eq_sj']
        have h_q_is_succ' : Γ ⊢ q =eq succ (add (succ k) j') := eq_trans h_q_eq_sk_sj' (spec (spec (ax5_add_succ) (t := j')) (t := succ k))
        exact ex_intro (add (succ k) j') h_q_is_succ'

    -- La ecuación se convierte en `a = a + σ(r)` para algún `r`.
    apply ex_elim h_q_is_succ; intro r; intro h_q_eq_sr
    have h_a_eq_a_sr : Γ ⊢ a =eq add a (succ r) := by rwa [h_q_eq_sr] at h_a_eq_aq

    -- Por la definición de `<` (Ax 13), esto implica `a < a`.
    have h_a_lt_a : Γ ⊢ a < a := (iff_mpr (spec (spec (ax13_lt_def (t₂ := a) (t₁ := a))))) (ex_intro r h_a_eq_a_sr)

    -- Esto contradice la irreflexividad (Ax 18).
    exact (spec (ax (by simp [axioms, ax18_lt_irrefl])) (t := a)) h_a_lt_a

  -- Con `¬(b < σ(a))` demostrado, usamos la tricotomía en `σ(a)` y `b`.
  let h_trichotomy := spec (spec (ax (by simp [axioms, ax19_lt_trichotomy])) (t := b)) (t := succ a)
  apply or_elim (or_elim h_trichotomy)
  · intro h_sa_lt_b -- Caso σ(a) < b
    exact or_intro_left _ h_sa_lt_b
  · intro h_sa_eq_b_or_b_lt_sa
    apply or_elim h_sa_eq_b_or_b_lt_sa
    · intro h_sa_eq_b -- Caso σ(a) = b
      exact or_intro_right _ h_sa_eq_b
    · intro h_b_lt_sa -- Caso b < σ(a)
      exact false_elim (h_not_b_lt_sa h_b_lt_sa)

-- Lema Auxiliar: a ≤ b ∧ c > 0 ⇒ a*c ≤ b*c
private theorem mul_le_mono_right {a b c : Term} (h_le : Γ ⊢ a ≤ b) (h_c_pos : Γ ⊢ zero < c) : Γ ⊢ (mul a c) ≤ (mul b c) := by
  -- Estrategia: Descomponer a ≤ b en a = b ∨ a < b.
  apply or_elim h_le
  · intro h_a_lt_b -- Caso a < b
    -- Queremos demostrar a*c ≤ b*c. Demostraremos el caso más fuerte a*c < b*c.
    -- 1. De a < b, existe d tal que b = a + σ(d).
    have h_ax13_ab := (iff_mp (spec (spec (ax13_lt_def (t₂ := a) (t₁ := b))))) h_a_lt_b
    apply ex_elim h_ax13_ab; intro d; intro h_b_eq_a_sd

    -- 2. Expandimos b*c = (a + σ(d))*c = a*c + σ(d)*c
    have h_bc_eq_ac_sdc : Γ ⊢ mul b c =eq add (mul a c) (mul (succ d) c) := by
      have h_comm_b := spec (spec (ax ax10_mul_comm) (t := c)) (t := b)
      have h_comm_a := spec (spec (ax ax10_mul_comm) (t := c)) (t := a)
      have h_comm_sd := spec (spec (ax ax10_mul_comm) (t := c)) (t := succ d)
      have h_distrib := spec (spec (spec (ax ax12_mul_distrib) (t := succ d)) (t := a)) (t := c)
      have h1 := eq_trans h_comm_b (eq_congr_mul_left h_b_eq_a_sd)
      have h2 := eq_trans h1 h_distrib
      have h3 := eq_congr_add_right (eq_symm h_comm_a)
      have h4 := eq_congr_add_left (eq_symm h_comm_sd)
      exact eq_trans (eq_trans h2 h3) h4

    -- 3. Demostramos que σ(d)*c es un sucesor, ya que c > 0.
    have h_c_neq_zero : Γ ⊢ neg (c =eq zero) := mp (spec (spec ne_of_lt)) h_c_pos
    have h_c_is_succ : Γ ⊢ ex (succ (.var 0) =eq c) := mp (spec teo_3_11) h_c_neq_zero
    apply ex_elim h_c_is_succ; intro k; intro h_c_eq_sk
    have h_sdc_is_succ : Γ ⊢ ex (succ (.var 0) =eq mul (succ d) c) := by
      have h_sdc_eq_sdsk : Γ ⊢ mul (succ d) c =eq mul (succ d) (succ k) := eq_congr_mul_left h_c_eq_sk
      have h_term_eq_s : Γ ⊢ mul (succ d) (succ k) =eq succ (add (mul (succ d) k) d) := by
        have h_ax9 := spec (spec (ax ax9_mul_succ) (t := k)) (t := succ d)
        have h_ax5 := spec (spec (ax ax5_add_succ) (t := d)) (t := mul (succ d) k)
        exact eq_trans h_ax9 h_ax5
      exact ex_intro (add (mul (succ d) k) d) (eq_trans h_sdc_eq_sdsk h_term_eq_s)

    -- 4. Como σ(d)*c = σ(j) para algún j, tenemos a*c < a*c + σ(d)*c = b*c.
    apply ex_elim h_sdc_is_succ; intro j; intro h_sdc_eq_sj
    have h_lt_spec := spec (spec lt_add_succ (t := j)) (t := mul a c)
    have h_ac_lt_ac_sdc : Γ ⊢ lt (mul a c) (add (mul a c) (mul (succ d) c)) := eq_subst (eq_symm h_sdc_eq_sj) h_lt_spec
    have h_ac_lt_bc : Γ ⊢ lt (mul a c) (mul b c) := eq_subst h_bc_eq_ac_sdc h_ac_lt_ac_sdc
    exact or_intro_left _ h_ac_lt_bc

  · intro h_a_eq_b -- Caso a = b
    have h_ac_eq_bc : Γ ⊢ mul a c =eq mul b c := eq_congr_mul_right h_a_eq_b
    exact or_intro_right _ h_ac_eq_bc

-- Lema Auxiliar: a ≤ b ⇒ a² ≤ b²
private theorem sq_le_mono {a b : Term} (h_le : Γ ⊢ a ≤ b) : Γ ⊢ (sq a) ≤ (sq b) := by
  sorry -- Depends on mul_le_mono_right.

-- Lemas auxiliares de transitividad
private theorem lt_le_trans {a b c : Term} (h_lt : Γ ⊢ a < b) (h_le : Γ ⊢ b ≤ c) : Γ ⊢ a < c := by
  apply or_elim h_le
  · intro h_b_lt_c
    exact lt_trans (and_intro h_lt h_b_lt_c)
  · intro h_b_eq_c
    rwa [h_b_eq_c] at h_lt

theorem le_lt_trans {a b c : Term} (h_le : Γ ⊢ a ≤ b) (h_lt : Γ ⊢ b < c) : Γ ⊢ a < c := by
  apply or_elim h_le
  · intro h_a_lt_b
    exact lt_trans (and_intro h_a_lt_b h_lt)
  · intro h_a_eq_b
    rwa [h_a_eq_b] at h_lt

theorem le_trans {a b c : Term} (h_ab : Γ ⊢ a ≤ b) (h_bc : Γ ⊢ b ≤ c) : Γ ⊢ a ≤ c := by
  apply or_elim h_ab
  · intro h_a_lt_b
    exact or_intro_left _ (lt_le_trans h_a_lt_b h_bc)
  · intro h_a_eq_b
    rwa [h_a_eq_b] at h_bc

-- Teo 4.6: k² ≤ n ∧ n < (k+1)² ⇒ k = √n (Unicidad)
theorem sqrt_unique_of_bounds {k n : Term} : Γ ⊢ ((sq k) ≤ n) ∧ (n < (sq (succ k))) ⇒ (k =eq (sqrt n)) := by
  apply deduction_theorem; intro h_bounds
  have h_sq_k_le_n : Γ ⊢ (sq k) ≤ n := and_elim_left h_bounds
  have h_n_lt_sq_succ_k : Γ ⊢ n < (sq (succ k)) := and_elim_right h_bounds

  let s := sqrt n
  have h_trichotomy := spec (spec (ax (by simp [axioms, ax19_lt_trichotomy])) (t := s)) (t := k)

  apply or_elim (or_elim h_trichotomy)
  · intro h_k_lt_s -- Caso 1: k < s
    exfalso
    have h_succ_k_le_s : Γ ⊢ (succ k) ≤ s := succ_le_of_lt h_k_lt_s
    have h_sq_succ_k_le_sq_s : Γ ⊢ (sq (succ k)) ≤ (sq s) := sq_le_mono h_succ_k_le_s
    have h_sq_s_le_n : Γ ⊢ (sq s) ≤ n := sqrt_sq_le n
    have h_sq_succ_k_le_n : Γ ⊢ (sq (succ k)) ≤ n := le_trans h_sq_succ_k_le_sq_s h_sq_s_le_n
    have h_contra := lt_asymm h_n_lt_sq_succ_k
    apply or_elim h_sq_succ_k_le_n
    · intro h_lt -- sq (succ k) < n
      exact h_contra h_lt
    · intro h_eq -- sq (succ k) = n
      have h_n_lt_n : Γ ⊢ n < n := by rwa [h_eq] at h_n_lt_sq_succ_k
      exact (spec (ax ax18_lt_irrefl) (t := n)) h_n_lt_n
  · intro h_k_eq_s_or_s_lt_k -- k = s ∨ s < k
    apply or_elim h_k_eq_s_or_s_lt_k
    · intro h_k_eq_s -- Caso 2: k = s
      exact h_k_eq_s
    · intro h_s_lt_k -- Caso 3: s < k
      exfalso
      have h_succ_s_le_k : Γ ⊢ (succ s) ≤ k := succ_le_of_lt h_s_lt_k
      have h_sq_succ_s_le_sq_k : Γ ⊢ (sq (succ s)) ≤ (sq k) := sq_le_mono h_succ_s_le_k
      have h_n_lt_sq_succ_s : Γ ⊢ n < (sq (succ s)) := lt_succ_sqrt_sq n
      have h_n_lt_sq_k : Γ ⊢ n < (sq k) := le_lt_trans h_n_lt_sq_succ_s h_sq_succ_s_le_sq_k
      have h_contra := lt_asymm h_n_lt_sq_k
      apply or_elim h_sq_k_le_n
      · intro h_lt -- sq k < n
        exact h_contra h_lt
      · intro h_eq -- sq k = n
        have h_n_lt_n : Γ ⊢ n < n := by rwa [h_eq] at h_n_lt_sq_k
        exact (spec (ax ax18_lt_irrefl) (t := n)) h_n_lt_n

-- Teo 4.4: √0 = 0
theorem sqrt_zero : Γ ⊢ (sqrt 0) =eq 0 := by
  -- We prove this using Teo 4.6 (uniqueness) with k=0, n=0.
  -- We need to show: 0² ≤ 0 ∧ 0 < (0+1)²
  have h_sq_zero_le_zero : Γ ⊢ (sq zero) ≤ zero := by
    simp [sq, le]; apply or_intro_right
    exact ax8_mul_zero
  have h_zero_lt_sq_one : Γ ⊢ zero < (sq (succ zero)) := by
    have h_sq_one_eq_one : Γ ⊢ (sq (succ zero)) =eq one := by simp [sq, one, teo_1_8]
    rw [←h_sq_one_eq_one]
    exact zero_lt_one
  have h_bounds_hold : Γ ⊢ ((sq zero) ≤ zero) ∧ (zero < (sq (succ zero))) :=
    and_intro h_sq_zero_le_zero h_zero_lt_sq_one
  exact mp (sqrt_unique_of_bounds (k := zero) (n := zero)) h_bounds_hold

-- Teo 4.5: √1 = 1
theorem sqrt_one : Γ ⊢ (sqrt 1) =eq 1 := by
  -- We prove this using Teo 4.6 (uniqueness) with k=1, n=1.
  -- We need to show: 1² ≤ 1 ∧ 1 < (1+1)²
  have h_sq_one_le_one : Γ ⊢ (sq one) ≤ one := by
    simp [sq, le, teo_1_8]; apply or_intro_right; rfl
  have h_one_lt_sq_two : Γ ⊢ one < (sq (succ one)) := by
    have h_sq_two_eq_four : Γ ⊢ (sq (succ one)) =eq (succ (succ (succ one))) := by simp [sq, one, two, teo_1_10]
    rw [←h_sq_two_eq_four]
    apply lt_trans (and_intro one_lt_two (lt_trans (and_intro two_lt_three three_lt_four)))
  have h_bounds_hold : Γ ⊢ ((sq one) ≤ one) ∧ (one < (sq (succ one))) :=
    and_intro h_sq_one_le_one h_one_lt_sq_two
  exact mp (sqrt_unique_of_bounds (k := one) (n := one)) h_bounds_hold

end ROBINSON_PlusPlus.Minimal.Theorems.Block2

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block2 (
  sqrt_sq_le
  lt_succ_sqrt_sq
  sq_eq_zero_imp_zero
  sqrt_zero
  sqrt_one
  sqrt_unique_of_bounds
  succ_le_of_lt
  lt_le_trans
  le_lt_trans
  le_trans
)
