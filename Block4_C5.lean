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
import FOL.Metamath.Deduction

open FOL.FOL
open FOL.Tactics
open FOL.Theorems
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
  div2 (tau (sqrt (add (mul eight c) one)))

-- Lema Auxiliar: ∀ n, 2*div2(n) ≤ n
private theorem lemma_2_div2_le_n (n : Term) : Γ ⊢ le (mul two (div2 n)) n := by
  have h_range := spec mod2_range (t := n)
  apply or_elim h_range
  · intro h_mod2_eq_0 -- Caso mod2(n) = 0
    have h_ax17 := spec (ax ax17_div_mod_eq) (t := n)
    have h_n_eq_2div2n : Γ ⊢ n =eq mul (div2 n) two := by
      have h1 := eq_trans (eq_congr_add_left h_mod2_eq_0) h_ax17
      have h2 := spec (ax ax4_add_zero) (t := mul (div2 n) two)
      rw [←h2] at h1
      exact eq_symm h1
    have h_comm := spec (spec (ax ax10_mul_comm) (t := two)) (t := div2 n)
    have h_2div2n_eq_n : Γ ⊢ mul two (div2 n) =eq n := eq_trans h_comm (eq_symm h_n_eq_2div2n)
    exact or_intro_right _ h_2div2n_eq_n
  · intro h_mod2_eq_1 -- Caso mod2(n) = 1
    have h_ax17 := spec (ax ax17_div_mod_eq) (t := n)
    have h_n_eq_2div2n_add_1 : Γ ⊢ n =eq add (mul (div2 n) two) one := by
      exact eq_symm (eq_trans (eq_congr_add_left h_mod2_eq_1) (eq_symm h_ax17))
    have h_comm := spec (spec (ax ax10_mul_comm) (t := two)) (t := div2 n)
    have h_n_eq_add_1 : Γ ⊢ n =eq add (mul two (div2 n)) one := eq_trans h_n_eq_2div2n_add_1 (eq_congr_add_right h_comm)
    have h_teo2_8 := spec teo_2_8 (t := mul two (div2 n))
    have h_n_eq_succ : Γ ⊢ n =eq succ (mul two (div2 n)) := eq_trans h_n_eq_add_1 (eq_symm h_teo2_8)
    have h_lt := spec lt_succ_self (t := mul two (div2 n))
    have h_lt_n : Γ ⊢ lt (mul two (div2 n)) n := by rwa [←h_n_eq_succ]
    exact or_intro_left _ h_lt_n

-- Lema Auxiliar: (2w)² = 4w²
private theorem sq_mul_two (w : Term) : Γ ⊢ sq (mul two w) =eq mul (mul two two) (sq w) := by
  let four := mul two two
  have h_sq_2w : Γ ⊢ sq (mul two w) =eq mul (mul two w) (mul two w) := by simp [sq]
  have h_assoc1 := spec (spec (spec (ax ax11_mul_assoc) (t:=w)) (t:=two)) (t:=mul two w)
  have h_comm_w2 := spec (spec (ax ax10_mul_comm) (t:=w)) (t:=two)
  have h_assoc2 := spec (spec (spec (ax ax11_mul_assoc) (t:=two)) (t:=w)) (t:=w)
  have h_assoc3 := spec (spec (spec (ax ax11_mul_assoc) (t:=sq w)) (t:=two)) (t:=two)
  have h_comm_2sqw := spec (spec (ax ax10_mul_comm) (t:=sq w)) (t:=two)

  have h1 : Γ ⊢ mul (mul two w) (mul two w) =eq mul two (mul w (mul two w)) := by
    exact eq_symm (spec (spec (spec (ax ax11_mul_assoc) (t:=w)) (t:=two)) (t:=two))
  have h2 : Γ ⊢ mul w (mul two w) =eq mul w (mul w two) := eq_congr_mul_left h_comm_w2
  have h3 : Γ ⊢ mul w (mul w two) =eq mul (mul w w) two := by
    exact eq_symm (spec (spec (spec (ax ax11_mul_assoc) (t:=two)) (t:=w)) (t:=w))
  have h4 : Γ ⊢ mul (mul w w) two =eq mul (sq w) two := by simp [sq]
  have h5 : Γ ⊢ mul two (mul (sq w) two) =eq mul (mul two (sq w)) two := by
    exact eq_symm (spec (spec (spec (ax ax11_mul_assoc) (t:=two)) (t:=sq w)) (t:=two))
  have h6 : Γ ⊢ mul (mul two (sq w)) two =eq mul (mul (sq w) two) two := eq_congr_mul_right h_comm_2sqw
  have h7 : Γ ⊢ mul (mul (sq w) two) two =eq mul (sq w) (mul two two) := by
    exact spec (spec (spec (ax ax11_mul_assoc) (t:=two)) (t:=two)) (t:=sq w)
  have h8 : Γ ⊢ mul (sq w) four =eq mul four (sq w) := by
    exact spec (spec (ax ax10_mul_comm) (t:=four)) (t:=sq w)

  have h_chain := eq_trans h1 (eq_congr_mul_left (eq_trans h2 (eq_trans h3 h4)))
  have h_chain2 := eq_trans h_chain (eq_trans h5 (eq_trans h6 (eq_trans h7 h8)))
  exact eq_trans h_sq_2w h_chain2

-- Lema Auxiliar: (2w+1)² = 4w² + 4w + 1
private theorem sq_2w_plus_1 (w : Term) : Γ ⊢ sq (add (mul two w) one) =eq add (add (mul (mul two two) (sq w)) (mul (mul two two) w)) one := by
  let four := mul two two
  have h_2w1_eq_s2w : Γ ⊢ add (mul two w) one =eq succ (mul two w) := eq_symm (spec teo_2_8 (t := mul two w))
  have h_lhs_eq_sq_s2w : Γ ⊢ sq (add (mul two w) one) =eq sq (succ (mul two w)) := eq_congr_sq h_2w1_eq_s2w
  have h_sq_sX_eq : Γ ⊢ sq (succ (mul two w)) =eq add (mul (succ (mul two w)) (mul two w)) (succ (mul two w)) :=
    spec (spec (ax ax9_mul_succ) (t := mul two w)) (t := succ (mul two w))
  have h_comm := spec (spec (ax ax10_mul_comm) (t := mul two w)) (t := succ (mul two w))
  have h_sq_sX_eq' : Γ ⊢ sq (succ (mul two w)) =eq add (mul (mul two w) (succ (mul two w))) (succ (mul two w)) := eq_trans h_sq_sX_eq (eq_congr_add_left h_comm)
  have h_mul_sX_eq : Γ ⊢ mul (mul two w) (succ (mul two w)) =eq add (mul (mul two w) (mul two w)) (mul two w) :=
    spec (spec (ax ax9_mul_succ) (t := mul two w)) (t := mul two w)
  have h_sq_sX_eq'' : Γ ⊢ sq (succ (mul two w)) =eq add (add (sq (mul two w)) (mul two w)) (succ (mul two w)) := by
    simp [sq] at h_mul_sX_eq; exact eq_trans h_sq_sX_eq' (eq_congr_add_left h_mul_sX_eq)
  have h_4w_sq := sq_mul_two w
  have h_sq_sX_eq''' : Γ ⊢ sq (succ (mul two w)) =eq add (add (mul four (sq w)) (mul two w)) (succ (mul two w)) :=
    eq_trans h_sq_sX_eq'' (eq_congr_add_left (eq_congr_add_right h_4w_sq))
  have h_assoc := spec (spec (spec (ax ax7_add_assoc) (t := succ (mul two w))) (t := mul two w)) (t := mul four (sq w))
  have h_sq_sX_eq'''' : Γ ⊢ sq (succ (mul two w)) =eq add (mul four (sq w)) (add (mul two w) (succ (mul two w))) := eq_trans h_sq_sX_eq''' h_assoc
  have h_2w_s2w : Γ ⊢ add (mul two w) (succ (mul two w)) =eq succ (add (mul two w) (mul two w)) :=
    spec (spec (ax ax5_add_succ) (t := mul two w)) (t := mul two w)
  have h_2w_2w_eq_4w : Γ ⊢ add (mul two w) (mul two w) =eq mul four w := by
    have h1 := eq_symm (spec teo_2_7 (t := mul two w))
    have h2 := eq_congr_mul_left (spec teo_2_7 (t := w))
    have h3 := spec (spec (spec (ax ax11_mul_assoc) (t:=w))(t:=two))(t:=two)
    exact eq_trans h1 (eq_trans h2 h3)
  have h_s_4w_eq_4w1 : Γ ⊢ succ (mul four w) =eq add (mul four w) one := eq_symm (spec teo_2_8 (t := mul four w))
  have h_final_assoc := spec (spec (spec (ax ax7_add_assoc) (t := one)) (t := mul four w)) (t := mul four (sq w))
  have h_chain := eq_trans h_2w_s2w (eq_congr_succ h_2w_2w_eq_4w)
  have h_chain2 := eq_trans h_chain h_s_4w_eq_4w1
  exact eq_trans h_sq_sX_eq'''' (eq_trans (eq_congr_add_left h_chain2) h_final_assoc)

-- Lema Auxiliar: a+1 ≤ b+1 → a ≤ b
private theorem le_of_succ_le_succ {a b : Term} (h : Γ ⊢ (succ a) ≤ (succ b)) : Γ ⊢ a ≤ b := by
  apply or_elim h
  · intro h_sa_lt_sb -- succ a < succ b
    have h_exists_k := (iff_mp (spec (spec ax13_lt_def (t₂ := succ a)) (t₁ := succ b))) h_sa_lt_sb
    apply ex_elim h_exists_k; intro k; intro h_eq
    have h_ax5 := spec (spec (ax ax5_add_succ) (t := k)) (t := succ a)
    have h_rhs_eq_s_sak : Γ ⊢ add (succ a) (succ k) =eq succ (add (succ a) k) := h_ax5
    have h_sb_eq_s_sak : Γ ⊢ succ b =eq succ (add (succ a) k) := eq_trans h_eq h_rhs_eq_s_sak
    have h_b_eq_sak : Γ ⊢ b =eq add (succ a) k := mp (spec (spec (ax ax3_peano_succ_inj) (t := add (succ a) k)) (t := b)) h_sb_eq_s_sak
    have h_ax6 := spec (spec (ax ax6_add_comm) (t := k)) (t := succ a)
    have h_b_eq_k_sa : Γ ⊢ b =eq add k (succ a) := eq_trans h_b_eq_sak h_ax6
    have h_ax5' := spec (spec (ax ax5_add_succ) (t := a)) (t := k)
    have h_b_eq_s_ka : Γ ⊢ b =eq succ (add k a) := eq_trans h_b_eq_k_sa h_ax5'
    have h_ax6' := spec (spec (ax ax6_add_comm) (t := a)) (t := k)
    have h_b_eq_s_ak : Γ ⊢ b =eq succ (add a k) := eq_trans h_b_eq_s_ka (eq_congr_succ h_ax6')
    have h_ax5'' := spec (spec (ax ax5_add_succ) (t := k)) (t := a)
    have h_b_eq_a_sk : Γ ⊢ b =eq add a (succ k) := eq_trans h_b_eq_s_ak (eq_symm h_ax5'')
    have h_a_lt_b := (iff_mpr (spec (spec ax13_lt_def (t₂ := a)) (t₁ := b))) (ex_intro k h_b_eq_a_sk)
    exact or_intro_left _ h_a_lt_b
  · intro h_sa_eq_sb -- succ a = succ b
    have h_a_eq_b : Γ ⊢ a =eq b := mp (spec (spec (ax ax3_peano_succ_inj) (t := b)) (t := a)) h_sa_eq_sb
    exact or_intro_right _ h_a_eq_b

-- Lema Auxiliar: a ≤ b → a+1 ≤ b+1
private theorem succ_le_succ_of_le {a b : Term} (h : Γ ⊢ a ≤ b) : Γ ⊢ (succ a) ≤ (succ b) := by
  apply or_elim h
  · intro h_a_lt_b -- a < b
    have h_sa_le_b : Γ ⊢ succ a ≤ b := succ_le_of_lt h_a_lt_b
    have h_b_lt_sb : Γ ⊢ b < succ b := lt_succ_self b
    have h_sa_lt_sb : Γ ⊢ succ a < succ b := le_lt_trans h_sa_le_b h_b_lt_sb
    exact or_intro_left _ h_sa_lt_sb
  · intro h_a_eq_b -- a = b
    have h_sa_eq_sb : Γ ⊢ succ a =eq succ b := eq_congr_succ h_a_eq_b
    exact or_intro_right _ h_sa_eq_sb

-- Lema Auxiliar: a ≤ b → a+c ≤ b+c
private theorem le_add_const_of_le {a b c : Term} (h : Γ ⊢ a ≤ b) : Γ ⊢ add a c ≤ add b c := by
  apply or_elim h
  · intro h_a_lt_b -- a < b
    have h_exists_k := (iff_mp (spec (spec ax13_lt_def (t₂ := a)) (t₁ := b))) h_a_lt_b
    apply ex_elim h_exists_k; intro k; intro h_b_eq_a_sk
    have h_bc_eq_ac_sk : Γ ⊢ add b c =eq add (add a c) (succ k) := by
      have h1 := eq_congr_add_right h_b_eq_a_sk
      have h2 := spec (spec (spec (ax ax7_add_assoc) (t:=c)) (t:=succ k)) (t:=a)
      have h3 := eq_trans h1 h2
      have h4 := eq_congr_add_left (spec (spec (ax ax6_add_comm) (t:=c)) (t:=succ k))
      have h5 := eq_trans h3 h4
      have h6 := eq_symm (spec (spec (spec (ax ax7_add_assoc) (t:=succ k)) (t:=c)) (t:=a))
      exact eq_trans h5 h6
    have h_lt := spec (spec lt_add_succ (t := k)) (t := add a c)
    exact or_intro_left _ (eq_subst h_bc_eq_ac_sk h_lt)
  · intro h_a_eq_b -- a = b
    exact or_intro_right _ (eq_congr_add_right h_a_eq_b)

-- Lema Auxiliar: a ≤ b → c+a ≤ c+b
private theorem le_add_const_of_le_left {a b c : Term} (h : Γ ⊢ a ≤ b) : Γ ⊢ add c a ≤ add c b := by
  have h_ca_eq_ac : Γ ⊢ add c a =eq add a c := spec (spec (ax ax6_add_comm) (t := a)) (t := c)
  have h_ac_le_bc : Γ ⊢ add a c ≤ add b c := le_add_const_of_le h
  have h_bc_eq_cb : Γ ⊢ add b c =eq add c b := spec (spec (ax ax10_mul_comm) (t := c)) (t := b)
  rw [←h_ca_eq_ac, ←h_bc_eq_cb] at h_ac_le_bc
  exact h_ac_le_bc

-- Lema Auxiliar: a < b ∧ c > 0 → a*c < b*c
private theorem mul_lt_mono_right {a b c : Term} (h_lt : Γ ⊢ a < b) (h_c_pos : Γ ⊢ lt zero c) : Γ ⊢ (mul a c) < (mul b c) := by
  have h_exists_d := (iff_mp (spec (spec ax13_lt_def (t₂ := a)) (t₁ := b))) h_lt
  apply ex_elim h_exists_d; intro d; intro h_b_eq_a_sd
  have h_bc_eq_ac_sdc : Γ ⊢ mul b c =eq add (mul a c) (mul (succ d) c) := by
    have h_comm_b := spec (spec (ax ax10_mul_comm) (t := c)) (t := b)
    have h1 := eq_trans h_comm_b (eq_congr_mul_left h_b_eq_a_sd)
    have h_distrib := spec (spec (spec (ax ax12_mul_distrib) (t := succ d)) (t := a)) (t := c)
    have h2 := eq_trans h1 h_distrib
    have h_comm_ca := spec (spec (ax ax10_mul_comm) (t := a)) (t := c)
    have h_comm_csd := spec (spec (ax ax10_mul_comm) (t := succ d)) (t := c)
    have h3 := eq_congr_add_right (eq_symm h_comm_ca)
    have h4 := eq_congr_add_left (eq_symm h_comm_csd)
    exact eq_trans (eq_trans h2 h3) h4
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
  apply ex_elim h_sdc_is_succ; intro j; intro h_sdc_eq_sj
  have h_lt_spec := spec (spec lt_add_succ (t := j)) (t := mul a c)
  have h_ac_lt_ac_sdc : Γ ⊢ lt (mul a c) (add (mul a c) (mul (succ d) c)) := eq_subst (eq_symm h_sdc_eq_sj) h_lt_spec
  exact eq_subst h_bc_eq_ac_sdc h_ac_lt_ac_sdc

-- Lema Auxiliar: a*c ≤ b*c ∧ c > 0 → a ≤ b
private theorem le_of_mul_le_mul_right {a b c : Term} (h_le : Γ ⊢ le (mul a c) (mul b c)) (h_c_pos : Γ ⊢ lt zero c) : Γ ⊢ a ≤ b := by
  have h_trichotomy := spec (spec (ax ax19_lt_trichotomy) (t := b)) (t := a)
  apply or_elim (or_elim h_trichotomy)
  · intro h_a_lt_b; exact or_intro_left _ h_a_lt_b
  · intro h_a_eq_b_or_b_lt_a; apply or_elim h_a_eq_b_or_b_lt_a
    · intro h_a_eq_b; exact or_intro_right _ h_a_eq_b
    · intro h_b_lt_a; exfalso
      have h_bc_lt_ac := mul_lt_mono_right h_b_lt_a h_c_pos
      apply or_elim h_le
      · intro h_ac_lt_bc; exact (lt_asymm h_bc_lt_ac) h_ac_lt_bc
      · intro h_ac_eq_bc; have h_bc_lt_bc := by rwa [←h_ac_eq_bc] at h_bc_lt_ac; exact h_bc_lt_bc
        exact (spec (ax ax18_lt_irrefl) (t := mul b c)) h_bc_lt_bc

-- Lema Auxiliar: c*a ≤ c*b ∧ c > 0 → a ≤ b
private theorem le_of_mul_le_mul_left {a b c : Term} (h_le : Γ ⊢ le (mul c a) (mul c b)) (h_c_pos : Γ ⊢ lt zero c) : Γ ⊢ a ≤ b := by
  have h_ca_eq_ac : Γ ⊢ mul c a =eq mul a c := spec (spec (ax ax10_mul_comm) (t := a)) (t := c)
  have h_cb_eq_bc : Γ ⊢ mul c b =eq mul b c := spec (spec (ax ax10_mul_comm) (t := b)) (t := c)
  have h_ac_le_bc : Γ ⊢ le (mul a c) (mul b c) := by
    apply or_elim h_le
    · intro h_ca_lt_cb -- mul c a < mul c b
      have h1 := eq_trans (eq_symm h_ca_eq_ac) h_ca_lt_cb
      exact or_intro_left _ (eq_trans h1 h_cb_eq_bc)
    · intro h_ca_eq_cb -- mul c a = mul c b
      have h1 := eq_trans h_ca_eq_ac h_ca_eq_cb
      exact or_intro_right _ (eq_trans h1 (eq_symm h_cb_eq_bc))
  exact le_of_mul_le_mul_right h_ac_le_bc h_c_pos

-- Lema Auxiliar: a < b → c+a < c+b
private theorem lt_add_const_of_le_left {a b c : Term} (h : Γ ⊢ a < b) : Γ ⊢ add c a < add c b := by
  have h_ca_eq_ac : Γ ⊢ add c a =eq add a c := spec (spec (ax ax6_add_comm) (t := a)) (t := c)
  have h_ac_lt_bc : Γ ⊢ add a c < add b c := lt_add_const_of_le h
  have h_bc_eq_cb : Γ ⊢ add b c =eq add c b := spec (spec (ax ax6_add_comm) (t := c)) (t := b)
  rw [←h_ca_eq_ac, ←h_bc_eq_cb] at h_ac_lt_bc
  exact h_ac_lt_bc

-- Lema Auxiliar: a < b → a² < b²
private theorem sq_lt_mono {a b : Term} (h_lt : Γ ⊢ a < b) : Γ ⊢ sq a < sq b := by
  have h_a_ge_0 := zero_le a
  have h_b_pos : Γ ⊢ lt zero b := le_lt_trans h_a_ge_0 h_lt
  apply or_elim (spec (spec (ax ax20_eq_decidable) (t:=zero)) (t:=a))
  · intro h_a_eq_0 -- a = 0
    rw [h_a_eq_0]
    have h_sq_0_eq_0 : Γ ⊢ sq zero =eq zero := by simp [sq, ax8_mul_zero]
    rw [h_sq_0_eq_0]
    -- Goal: 0 < b²
    have h_b_sq_eq_0_iff_b_eq_0 := iff_intro (sq_eq_zero_imp_zero b) (by intro h; rw[h]; simp[sq, ax8_mul_zero])
    have h_b_neq_0 := mp (spec ne_of_lt) h_b_pos
    have h_b_sq_neq_0 := iff_false_left h_b_sq_eq_0_iff_b_eq_0 h_b_neq_0
    exact or_elim (zero_le (sq b))
    · intro h_0_lt_sq_b; exact h_0_lt_sq_b
    · intro h_0_eq_sq_b; exfalso; exact h_b_sq_neq_0 (eq_symm h_0_eq_sq_b)
  · intro h_a_neq_0 -- a > 0
    have h_a_pos : Γ ⊢ lt zero a := or_elim (zero_le a) (by intro h; exact h) (by intro h; exfalso; exact h_a_neq_zero (eq_symm h))
    have h_sq_a_lt_ab : Γ ⊢ sq a < mul a b := by
      simp [sq]; exact mul_lt_mono_left h_lt h_a_pos
    have h_ab_lt_sq_b : Γ ⊢ mul a b < sq b := by
      simp [sq]; exact mul_lt_mono_right h_lt h_b_pos
    exact lt_trans (and_intro h_sq_a_lt_ab h_ab_lt_sq_b)

-- Lema Auxiliar: a ≤ b → a(a+1) ≤ b(b+1)
private theorem mono_w_w1 {a b : Term} (h_le : Γ ⊢ a ≤ b) : Γ ⊢ le (mul a (succ a)) (mul b (succ b)) := by
  let g (n : Term) := mul n (succ n)
  have h_g_eq_sq_add (n : Term) : Γ ⊢ g n =eq add (sq n) n := w_mul_w_plus_one_eq_sq_w_add_w n
  rw [←h_g_eq_sq_add a, ←h_g_eq_sq_add b]
  -- Goal: a²+a ≤ b²+b
  apply or_elim h_le
  · intro h_a_lt_b -- a < b
    have h_sq_a_lt_sq_b : Γ ⊢ lt (sq a) (sq b) := sq_lt_mono h_a_lt_b
    have h_sq_a_add_a_lt_sq_b_add_a : Γ ⊢ lt (add (sq a) a) (add (sq b) a) := lt_add_const_of_le_left h_sq_a_lt_sq_b
    have h_sq_b_add_a_lt_sq_b_add_b : Γ ⊢ lt (add (sq b) a) (add (sq b) b) := lt_add_const_of_le h_a_lt_b
    exact or_intro_left _ (lt_trans (and_intro h_sq_a_add_a_lt_sq_b_add_a h_sq_b_add_a_lt_sq_b_add_b))
  · intro h_a_eq_b -- a = b
    exact or_intro_right _ (eq_congr_add (eq_congr_sq h_a_eq_b) h_a_eq_b)

-- Lema Auxiliar: w(w+1) ≤ 2c ↔ (2w+1)² ≤ 8c+1
private theorem w_w1_le_2c_iff_sq_2w1_le_8c1 {w c : Term} : Γ ⊢ (le (mul w (succ w)) (mul two c)) ↔ (le (sq (add (mul two w) one)) (add (mul eight c) one)) := by
  let four := mul two two
  have h_4_pos : Γ ⊢ lt zero four := by
    have h1 := lt_trans (and_intro zero_lt_one one_lt_two)
    have h2 := lt_trans (and_intro two_lt_three three_lt_four)
    exact lt_trans (and_intro h1 h2)

  apply iff_intro
  · -- (→)
    intro h_w_le_2c
    have h_4w_le_8c : Γ ⊢ le (mul four (mul w (succ w))) (mul four (mul two c)) :=
      mul_le_mono_left h_w_le_2c h_4_pos
    have h_lhs_expand : Γ ⊢ mul four (mul w (succ w)) =eq add (mul four (sq w)) (mul four w) := by
      have h1 := eq_congr_mul_left (w_mul_w_plus_one_eq_sq_w_add_w w)
      have h2 := spec (spec (spec (ax ax12_mul_distrib) (t:=w)) (t:=sq w)) (t:=four)
      exact eq_trans h1 h2
    have h_rhs_expand : Γ ⊢ mul four (mul two c) =eq mul eight c := by
      have h1 := eq_symm (spec (spec (spec (ax ax11_mul_assoc) (t:=c)) (t:=two)) (t:=four))
      have h2 : Γ ⊢ mul four two =eq eight := by simp [eight, four]; exact teo_1_10
      exact eq_trans h1 (eq_congr_mul_right h2)
    have h_4wsq_4w_le_8c : Γ ⊢ le (add (mul four (sq w)) (mul four w)) (mul eight c) := by
      rwa [←h_lhs_expand, ←h_rhs_expand] at h_4w_le_8c
    have h_add_1 : Γ ⊢ le (add (add (mul four (sq w)) (mul four w)) one) (add (mul eight c) one) :=
      le_add_const_of_le h_4wsq_4w_le_8c
    have h_sq_form := sq_2w_plus_1 w
    rwa [←h_sq_form] at h_add_1
  · -- (←)
    intro h_sq_le
    have h_sq_form := sq_2w_plus_1 w
    have h_alg_le : Γ ⊢ le (add (add (mul four (sq w)) (mul four w)) one) (add (mul eight c) one) := by
      rwa [h_sq_form] at h_sq_le
    have h_cancel_1 : Γ ⊢ le (add (mul four (sq w)) (mul four w)) (mul eight c) :=
      le_of_add_le_add_right h_alg_le
    have h_distrib_rev : Γ ⊢ add (mul four (sq w)) (mul four w) =eq mul four (add (sq w) w) :=
      eq_symm (spec (spec (spec (ax ax12_mul_distrib) (t:=w)) (t:=sq w)) (t:=four))
    have h_w_form_rev : Γ ⊢ add (sq w) w =eq mul w (succ w) := eq_symm (w_mul_w_plus_one_eq_sq_w_add_w w)
    have h_lhs_rev : Γ ⊢ add (mul four (sq w)) (mul four w) =eq mul four (mul w (succ w)) :=
      eq_trans h_distrib_rev (eq_congr_mul_left h_w_form_rev)
    have h_rhs_rev : Γ ⊢ mul eight c =eq mul four (mul two c) := by
      have h1 : Γ ⊢ mul eight c =eq mul (mul four two) c := by simp [eight, four]; rw [teo_1_10]
      exact eq_trans h1 (spec (spec (spec (ax ax11_mul_assoc) (t:=c)) (t:=two)) (t:=four))
    have h_4ww1_le_4_2c : Γ ⊢ le (mul four (mul w (succ w))) (mul four (mul two c)) := by
      rwa [←h_lhs_rev, ←h_rhs_rev] at h_cancel_1
    exact le_of_mul_le_mul_left h_4ww1_le_4_2c h_4_pos

-- Lema Auxiliar: n ≥ 1 → √n > 0
private theorem sqrt_of_ge_1_is_pos {n : Term} (h_n_ge_1 : Γ ⊢ le one n) : Γ ⊢ lt zero (sqrt n) := by
  let s := sqrt n
  have h_ax20_s0 := spec (spec (ax ax20_eq_decidable) (t := zero)) (t := s)
  apply or_elim h_ax20_s0
  · intro h_s_eq_0 -- Assume s = 0
    exfalso
    have h_n_lt_s1_sq := lt_succ_sqrt_sq n
    have h_s1_eq_1 : Γ ⊢ succ s =eq one := eq_congr_succ h_s_eq_0
    have h_s1_sq_eq_1 : Γ ⊢ sq (succ s) =eq one := by
      have h1 := eq_congr_sq h_s1_eq_1
      have h2 := spec teo_1_8
      exact eq_trans h1 h2
    have h_n_lt_1 : Γ ⊢ lt n one := by rwa [h_s1_sq_eq_1] at h_n_lt_s1_sq
    have h_not_n_lt_1 : Γ ⊢ neg (lt n one) := by
      apply or_elim h_n_ge_1
      · intro h_1_lt_n; exact lt_asymm h_1_lt_n
      · intro h_1_eq_n; rw [h_1_eq_n]; exact lt_irrefl one
    exact h_not_n_lt_1 h_n_lt_1
  · intro h_s_neq_0 -- Assume s ≠ 0
    exact or_elim (zero_le s)
    · intro h_0_lt_s; exact h_0_lt_s
    · intro h_0_eq_s; exfalso; exact h_s_neq_0 (eq_symm h_0_eq_s)

-- Teo 9.1 (Lema C5): ∀ c, ∃! w, w*(w+1) ≤ 2*c < (w+1)*(w+2)
theorem lemma_C5 (c : Term) : Γ ⊢ ex1 (land (le (mul (.var 0) (succ (.var 0))) (mul two c)) (lt (mul two c) (mul (succ (.var 0)) (succ (succ (.var 0)))))) := by
  -- Part 1: Existence. We show that `w_candidate c` satisfies the inequalities.
  let w := w_candidate c

  have h_existence_part1 : Γ ⊢ le (mul w (succ w)) (mul two c) := by
    -- Using `w_w1_le_2c_iff_sq_2w1_le_8c1`, this is equivalent to `(2w+1)² ≤ 8c+1`.
    apply (iff_mpr (w_w1_le_2c_iff_sq_2w1_le_8c1 (w := w) (c := c)))

    let s := sqrt (add (mul eight c) one)
    let p := tau s

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
        have h_ax26 := spec (ax ax26_tau_succ) (t := p_witness)
        simp [p, tau]; rwa [h_s_eq_spw] at h_ax26
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
      let p := tau s

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
        have h_ax26 := spec (ax ax26_tau_succ) (t := p_witness)
        simp [p, tau]; rwa [h_s_eq_spw] at h_ax26
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

  exact ex1_intro w h_existence h_uniqueness

end ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5 (
  w_candidate
  lemma_C5
)
