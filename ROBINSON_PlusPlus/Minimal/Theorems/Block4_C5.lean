/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block2
import ROBINSON_PlusPlus.Minimal.Theorems.Block3

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1
open ROBINSON_PlusPlus.Minimal.Theorems.Block2
open ROBINSON_PlusPlus.Minimal.Theorems.Block3

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5

/-!
## BLOQUE IV — LEMA C5 (INVERSIÓN DE CANTOR)
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 9.1: Lema C5 - Existencia y Unicidad de `w`
-/

-- Candidate for `w`
def w_candidate (c : Term) : Term :=
  div2 (pred (sqrt (add (mul eight c) one)))

-- Lema Auxiliar: ∀ n, 2*div2(n) ≤ n
private theorem lemma_2_div2_le_n (n : Term) : Γ ⊢ le (mul two (div2 n)) n := by sorry

-- Lema Auxiliar: (2w)² = 4w²
private theorem sq_mul_two (w : Term) : Γ ⊢ (sq (mul two w) =eq mul (mul two two) (sq w)) := by sorry

-- Lema Auxiliar: (2w+1)² = 4w² + 4w + 1
private theorem sq_2w_plus_1 (w : Term) : Γ ⊢ (sq (add (mul two w) one) =eq add (add (mul (mul two two) (sq w)) (mul (mul two two) w)) one) := by sorry

-- Lema Auxiliar: a+1 ≤ b+1 → a ≤ b
private theorem le_of_succ_le_succ {a b : Term} (h : Γ ⊢ ((succ a) ≤ (succ b))) : Γ ⊢ (a ≤ b) := by sorry

-- Lema Auxiliar: a ≤ b → a+1 ≤ b+1
private theorem succ_le_succ_of_le {a b : Term} (h : Γ ⊢ (a ≤ b)) : Γ ⊢ ((succ a) ≤ (succ b)) := by sorry

-- Lema Auxiliar: a ≤ b → a+c ≤ b+c
private theorem le_add_const_of_le {a b c : Term} (h : Γ ⊢ (a ≤ b)) : Γ ⊢ (add a c ≤ add b c) := by sorry

-- Lema Auxiliar: a ≤ b → c+a ≤ c+b
private theorem le_add_const_of_le_left {a b c : Term} (h : Γ ⊢ (a ≤ b)) : Γ ⊢ (add c a ≤ add c b) := by sorry

-- Lema Auxiliar: a < b ∧ c > 0 → a*c < b*c
private theorem mul_lt_mono_right {a b c : Term} (h_lt : Γ ⊢ lt a b) (h_c_pos : Γ ⊢ lt zero c) : Γ ⊢ lt (mul a c) (mul b c) := by sorry

-- Lema Auxiliar: a*c ≤ b*c ∧ c > 0 → a ≤ b
private theorem le_of_mul_le_mul_right {a b c : Term} (h_le : Γ ⊢ le (mul a c) (mul b c)) (h_c_pos : Γ ⊢ lt zero c) : Γ ⊢ (a ≤ b) := by sorry

-- Lema Auxiliar: c*a ≤ c*b ∧ c > 0 → a ≤ b
private theorem le_of_mul_le_mul_left {a b c : Term} (h_le : Γ ⊢ le (mul c a) (mul c b)) (h_c_pos : Γ ⊢ lt zero c) : Γ ⊢ (a ≤ b) := by sorry

-- Lema Auxiliar: a < b → c+a < c+b
private theorem lt_add_const_of_le_left {a b c : Term} (h : Γ ⊢ lt a b) : Γ ⊢ lt (add c a) (add c b) := by sorry

-- Lema Auxiliar: a < b → a² < b²
private theorem sq_lt_mono {a b : Term} (h_lt : Γ ⊢ lt a b) : Γ ⊢ lt (sq a) (sq b) := by sorry

-- Lema Auxiliar: a ≤ b → a(a+1) ≤ b(b+1)
private theorem mono_w_w1 {a b : Term} (h_le : Γ ⊢ (a ≤ b)) : Γ ⊢ le (mul a (succ a)) (mul b (succ b)) := by sorry

-- Lema Auxiliar: w(w+1) ≤ 2c ↔ (2w+1)² ≤ 8c+1
private theorem w_w1_le_2c_iff_sq_2w1_le_8c1 {w c : Term} :
    (Γ ⊢ le (mul w (succ w)) (mul two c)) ↔ (Γ ⊢ le (sq (add (mul two w) one)) (add (mul eight c) one)) := by sorry

-- Lema Auxiliar: n ≥ 1 → √n > 0
private theorem sqrt_of_ge_1_is_pos {n : Term} (h_n_ge_1 : Γ ⊢ le one n) : Γ ⊢ lt zero (sqrt n) := by sorry

-- Teo 9.1 (Lema C5): ∀ c, ∃! w, w*(w+1) ≤ 2*c < (w+1)*(w+2)
theorem lemma_C5 (c : Term) : Γ ⊢ Formula.ex (land (le (mul (.var 0) (succ (.var 0))) (mul two c)) (lt (mul two c) (mul (succ (.var 0)) (succ (succ (.var 0)))))) := by sorry
/-
  -- Part 1: Existence. We show that `w_candidate c` satisfies the inequalities.
  let w := w_candidate c

  have h_existence_part1 : Γ ⊢ le (mul w (succ w)) (mul two c) := by
    -- Using `w_w1_le_2c_iff_sq_2w1_le_8c1`, this is equivalent to `(2w+1)² ≤ 8c+1`.
    apply (iff_mpr (w_w1_le_2c_iff_sq_2w1_le_8c1 (w := w) (c := c)))

    let s := sqrt (add (mul eight c) one)
    let p := pred s

    -- From `sqrt` axiom, `s² ≤ 8c+1`. We prove `(2w+1)² ≤ s²` and use transitivity.
    apply le_trans (c := sq s)
    · -- Prove (2w+1)² ≤ s²
      apply sq_le_mono
      -- Prove 2w+1 ≤ s
      have h_w_eq_div2p : Γ ⊢ w =eq div2 p := by simp [w_candidate, w, p]
      rw [h_w_eq_div2p]

      -- We need s > 0 to establish s = σ(p).
      have h_8c1_ge_1 : Γ ⊢ le one (add (mul eight c) one) := by
        have h_zero_le_8c := zero_le (mul eight c)
        have h_1_le_8c1 := le_add_const_of_le_left h_zero_le_8c
        have h_1_eq_s0 := eq_symm (spec teo_2_8 (t := zero))
        have h_0_add_1_eq_1 := eq_trans (spec (ax ax4_add_zero) (t:=one)) (eq_symm h_1_eq_s0)
        rwa [←h_0_add_1_eq_1] at h_1_le_8c1
      have h_s_pos : Γ ⊢ lt zero s := sqrt_of_ge_1_is_pos h_8c1_ge_1
      have h_s_is_succ : Γ ⊢ ex (succ (.var 0) =eq s) := mp (spec teo_3_11) (mp (spec ne_of_lt) h_s_pos)

      -- Establish s = σ(p)
      apply ex_elim h_s_is_succ; intro p_witness; intro h_s_eq_spw
      have h_p_eq_pw : Γ ⊢ p =eq p_witness := by
        have h_ax26 := spec (ax ax26_pred_succ) (t := p_witness)
        simp [p, pred]; rwa [h_s_eq_spw] at h_ax26
      rw [←h_p_eq_pw] at h_s_eq_spw

      -- Goal is now `2*div2(p) + 1 ≤ σ(p)`
      have h_sp_eq_p1 : Γ ⊢ succ p =eq add p one := eq_symm (spec teo_2_8 (t := p))
      rw [h_s_eq_spw, h_sp_eq_p1]

      -- `2*div2(p) + 1 ≤ p+1` is equivalent to `2*div2(p) ≤ p`
      exact iff_mp (succ_le_succ_iff (a := mul two (div2 p)) (b := p)) (lemma_2_div2_le_n p)
    · -- Second part of transitivity: s² ≤ 8c+1
      exact sqrt_sq_le (add (mul eight c) one)

  have h_existence : Γ ⊢ land (le (mul w (succ w)) (mul two c)) (lt (mul two c) (mul (succ w) (succ (succ w)))) := by
    apply and_intro
    · exact h_existence_part1
    · -- Step 1.2: Prove the second inequality `2c < (w+1)(w+2)`
      -- This is equivalent to `8c+1 < (2w+3)²`.
      have h_equiv_lt : Γ ⊢ (lt (mul two c) (mul (succ w) (succ (succ w)))) ↔ (lt (add (mul eight c) one) (sq (add (mul two w) three))) := by sorry

      apply (iff_mp h_equiv_lt)
      -- Goal: 8c+1 < (2w+3)²
      let s := sqrt (add (mul eight c) one)
      let p := pred s

      -- From `sqrt` axiom, `8c+1 < (s+1)²`. We prove `(s+1)² ≤ (2w+3)²` and use transitivity.
      apply le_lt_trans (lt_succ_sqrt_sq (add (mul eight c) one))
      -- Goal: (s+1)² ≤ (2w+3)²
      apply sq_le_mono
      -- Goal: s+1 ≤ 2w+3
      have h_w_eq_div2p : Γ ⊢ w =eq div2 p := by simp [w_candidate, w, p]
      rw [h_w_eq_div2p]

      -- Establish s = σ(p)
      have h_8c1_ge_1 : Γ ⊢ le one (add (mul eight c) one) := by sorry
      have h_s_pos : Γ ⊢ lt zero s := sqrt_of_ge_1_is_pos h_8c1_ge_1
      have h_s_is_succ : Γ ⊢ ex (succ (.var 0) =eq s) := mp (spec teo_3_11) (mp (spec ne_of_lt) h_s_pos)
      apply ex_elim h_s_is_succ; intro p_witness; intro h_s_eq_spw
      have h_p_eq_pw : Γ ⊢ p =eq p_witness := by
        have h_ax26 := spec (ax ax26_pred_succ) (t := p_witness)
        simp [p, pred]; rwa [h_s_eq_spw] at h_ax26
      rw [←h_p_eq_pw] at h_s_eq_spw

      -- Goal is now `σ(p)+1 ≤ 2*div2(p)+3`
      -- which is `p+2 ≤ 2*div2(p)+3`
      -- which is `p ≤ 2*div2(p)+1`
      have h_p_le_2div2p1 := p_le_2div2p_plus_1 p
      have h_p1_le_2div2p2 := succ_le_succ_of_le h_p_le_2div2p1
      have h_p2_le_2div2p3 := succ_le_succ_of_le h_p1_le_2div2p2
      have h_s1_eq_p2 : Γ ⊢ add (succ s) one =eq add (succ (succ p)) one := eq_congr_add_right h_s_eq_spw
      have h_2w3_eq_2div2p3 : Γ ⊢ add (mul two (div2 p)) three =eq add (add (mul two (div2 p)) two) one := by sorry
      rwa [h_s_eq_spw, ←h_s1_eq_p2, ←h_2w3_eq_2div2p3] at h_p2_le_2div2p3

  have h_uniqueness : Γ ⊢ forall_ ( (land (le (mul (.var 0) (succ (.var 0))) (mul two c)) (lt (mul two c) (mul (succ (.var 0)) (succ (succ (.var 0)))))) ⇒ ((.var 0) =eq w) ) := by
    apply gen; intro w'
    apply imp_intro; intro h_w'_bounds
    have h_w_bounds := h_existence
    -- Goal: w' = w
    have h_trichotomy := spec (spec (ax ax19_lt_trichotomy) (t := w')) (t := w)
    apply or_elim (or_elim h_trichotomy)
    · intro h_w_lt_w' -- Case w < w'
      exfalso
      have h_w1_le_w' : Γ ⊢ succ w ≤ w' := succ_le_of_lt h_w_lt_w'
      have h_g_w1_le_g_w' : Γ ⊢ le (mul (succ w) (succ (succ w))) (mul w' (succ w')) := mono_w_w1 h_w1_le_w'
      have h_2c_lt_gw1 := and_elim_right h_w_bounds
      have h_gw'_le_2c := and_elim_left h_w'_bounds
      have h_lt_le := lt_le_trans h_2c_lt_gw1 h_g_w1_le_g_w'
      have h_2c_lt_2c := le_lt_trans h_gw'_le_2c h_lt_le
      exact (spec (ax ax18_lt_irrefl) (t := mul two c)) h_2c_lt_2c
    · intro h_w_eq_w'_or_w'_lt_w
      apply or_elim h_w_eq_w'_or_w'_lt_w
      · intro h_w_eq_w'; exact h_w_eq_w'
      · intro h_w'_lt_w -- Case w' < w
        exfalso
        have h_w'1_le_w : Γ ⊢ succ w' ≤ w := succ_le_of_lt h_w'_lt_w
        have h_g_w'1_le_g_w : Γ ⊢ le (mul (succ w') (succ (succ w'))) (mul w (succ w)) := mono_w_w1 h_w'1_le_w
        have h_2c_lt_gw'1 := and_elim_right h_w'_bounds
        have h_gw_le_2c := and_elim_left h_w_bounds
        have h_lt_le := lt_le_trans h_2c_lt_gw'1 h_g_w'1_le_g_w
        have h_2c_lt_2c := le_lt_trans h_gw_le_2c h_lt_le
        exact (spec (ax ax18_lt_irrefl) (t := mul two c)) h_2c_lt_2c

-/

end ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5 (
  w_candidate
  lemma_C5
)
