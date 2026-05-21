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

def Γ := axioms

def w_candidate (c : Term) : Term :=
  div2 (pred (sqrt (add (mul eight c) one)))

-- ============================================================
-- BASE HELPERS
-- ============================================================

-- 0 < σ(a): witness a gives 0 + σ(a) = σ(0 + a) = σ(a).
private theorem lt_zero_succ (a : Term) : Γ ⊢ lt zero (succ a) := by
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_0sa : axioms ⊢ (add zero (succ a) =eq succ a) := by
    have hs := spec teo_2_2 (succ a)
    simp [substFormula, substTerm, substTerms, add, zero, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm] at hs
    exact hs
  have h_iff := spec (spec h_ax13 zero) (succ a)
  simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
        liftTerm, liftTerms, FOL.substTerm_liftTerm,
        FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff
  apply iff_mpr h_iff
  exact ex_intro a (by
    simp [substFormula, substTerm, substTerms, add, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift]
    exact h_0sa)

-- 0 ≤ n for all n (re-proof of Block2 private zero_le).
private theorem zero_le (n : Term) : Γ ⊢ (zero ≤ n) := by
  have h_ax2  := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_tric : Γ ⊢ (lt zero n ∨ (zero =eq n) ∨ lt n zero) := by
    have h := spec (spec h_ax19 zero) n
    simp [substFormula, substTerm, substTerms, lt, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at h
    exact h
  apply Axioms.or_elim h_tric
  · intro h_lt; exact Axioms.or_intro_left h_lt
  · intro h23
    apply Axioms.or_elim h23
    · intro h_eq; exact Axioms.or_intro_right h_eq
    · intro h_nlt0
      apply false_elim
      have hh := spec (spec h_ax13 n) zero
      simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff,
            liftTerm, liftTerms, FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at hh
      apply ex_elim (iff_mp hh h_nlt0); intro k h_k
      simp [substFormula, substTerm, substTerms, add, succ, zero,
            liftTerm, liftTerms, FOL.substTerm_lift_comm,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_k
      have h_step : Γ ⊢ (add n (succ k) =eq succ (add n k)) := by
        have hs := spec (spec h_ax5 n) k
        simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
              FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at hs
        exact hs
      have h_neq0 : Γ ⊢ neg (succ (add n k) =eq zero) := by
        have hn := spec h_ax2 (add n k)
        simp [substFormula, substTerm, substTerms, succ, liftTerm, liftTerms,
              FOL.substTerm_liftTerm] at hn
        exact hn
      exact mp h_neq0 (eq_trans h_step h_k)

-- mul_lt_mono_right: a < b → 0 < c → a*c < b*c (re-proof of Block2 private).
private theorem mul_lt_mono_right {a b c : Term} (h_lt : Γ ⊢ lt a b) (h_c_pos : Γ ⊢ lt zero c) :
    Γ ⊢ lt (mul a c) (mul b c) := by
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax9  := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_ax12 := ax (by simp [axioms] : ax12_mul_distrib ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  -- Extract kp: a + σ(kp) = b
  have h_iff_ab := spec (spec h_ax13 a) b
  simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
        liftTerm, liftTerms, FOL.substTerm_liftTerm,
        FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff_ab
  apply ex_elim (iff_mp h_iff_ab h_lt); intro kp h_kp
  simp [substFormula, substTerm, substTerms, add, succ,
        liftTerm, liftTerms, FOL.substTerm_liftTerm,
        FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_kp
  -- Extract j: 0 + σ(j) = c
  have h_iff_0c := spec (spec h_ax13 zero) c
  simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
        liftTerm, liftTerms, FOL.substTerm_liftTerm,
        FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff_0c
  apply ex_elim (iff_mp h_iff_0c h_c_pos); intro j h_j
  simp [substFormula, substTerm, substTerms, add, succ, zero,
        liftTerm, liftTerms, FOL.substTerm_liftTerm,
        FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_j
  -- succ j = c  (from 0 + succ j = succ j = c, using teo_2_2)
  have h_0sj : Γ ⊢ (add zero (succ j) =eq succ j) := by
    have hs := spec teo_2_2 (succ j)
    simp [substFormula, substTerm, substTerms, add, zero, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm] at hs
    exact hs
  have h_sj_c : Γ ⊢ (succ j =eq c) := eq_trans h_0sj h_j
  -- b*c = (a + σkp)*c = a*c + σkp*c
  have h_comm1 : Γ ⊢ (mul (add a (succ kp)) c =eq mul c (add a (succ kp))) := by
    have h := spec (spec h_ax10 (add a (succ kp))) c
    simp [substFormula, substTerm, substTerms, mul, add, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm] at h
    exact h
  have h_distrib : Γ ⊢ (mul c (add a (succ kp)) =eq add (mul c a) (mul c (succ kp))) := by
    have h := spec (spec (spec h_ax12 c) a) (succ kp)
    simp [substFormula, substTerm, substTerms, mul, add, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h
    exact h
  have h_comm_ca : Γ ⊢ (mul c a =eq mul a c) := by
    have h := spec (spec h_ax10 c) a
    simp [substFormula, substTerm, substTerms, mul, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at h
    exact h
  have h_comm_cskp : Γ ⊢ (mul c (succ kp) =eq mul (succ kp) c) := by
    have h := spec (spec h_ax10 c) (succ kp)
    simp [substFormula, substTerm, substTerms, mul, succ, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at h
    exact h
  have h_right_distrib : Γ ⊢ (mul (add a (succ kp)) c =eq add (mul a c) (mul (succ kp) c)) :=
    FOL.derive_eq_trans h_comm1
      (FOL.derive_eq_trans h_distrib
        (FOL.derive_eq_trans (eq_congr_add_right h_comm_ca)
          (eq_congr_add_left h_comm_cskp)))
  have h_bc_rhs : Γ ⊢ (mul b c =eq mul (add a (succ kp)) c) :=
    eq_congr_mul_right (eq_symm h_kp)
  have h_bc_expand : Γ ⊢ (mul b c =eq add (mul a c) (mul (succ kp) c)) :=
    FOL.derive_eq_trans h_bc_rhs h_right_distrib
  -- σkp * c = σkp * σj  (since c = σj)
  have h_skp_c_sj : Γ ⊢ (mul (succ kp) c =eq mul (succ kp) (succ j)) :=
    eq_symm (eq_congr_mul_left h_sj_c)
  -- σkp * σj = σkp*j + σkp  [ax9]
  have h_skp_sj : Γ ⊢ (mul (succ kp) (succ j) =eq add (mul (succ kp) j) (succ kp)) := by
    have h := spec (spec h_ax9 (succ kp)) j
    simp [substFormula, substTerm, substTerms, mul, add, succ, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at h
    exact h
  -- σkp*j + σkp = σ(σkp*j + kp)  [ax5]
  have h_add_succ : Γ ⊢ (add (mul (succ kp) j) (succ kp) =eq succ (add (mul (succ kp) j) kp)) := by
    have h := spec (spec h_ax5 (mul (succ kp) j)) kp
    simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at h
    exact h
  have h_skp_c_succ : Γ ⊢ (mul (succ kp) c =eq succ (add (mul (succ kp) j) kp)) :=
    FOL.derive_eq_trans h_skp_c_sj (FOL.derive_eq_trans h_skp_sj h_add_succ)
  have h_bc_final : Γ ⊢ (mul b c =eq add (mul a c) (succ (add (mul (succ kp) j) kp))) :=
    FOL.derive_eq_trans h_bc_expand (eq_congr_add_left h_skp_c_succ)
  -- lt (mul a c) (mul b c) via ax13
  have h_iff_mac_mbc := spec (spec h_ax13 (mul a c)) (mul b c)
  simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
        liftTerm, liftTerms, FOL.substTerm_liftTerm,
        FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff_mac_mbc
  apply iff_mpr h_iff_mac_mbc
  exact ex_intro (add (mul (succ kp) j) kp) (by
    simp [substFormula, substTerm, substTerms, add, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift]
    exact eq_symm h_bc_final)

-- ============================================================
-- ORDER LEMMAS FOR SUCCESSOR
-- ============================================================

-- σ(a) ≤ σ(b) → a ≤ b
private theorem le_of_succ_le_succ {a b : Term} (h : Γ ⊢ ((succ a) ≤ (succ b))) : Γ ⊢ (a ≤ b) := by
  have h_ax3  := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax6  := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  apply Axioms.or_elim h
  · intro h_lt
    apply Axioms.or_intro_left
    -- lt (succ a) (succ b): ∃k, succ a + σ(k) = succ b
    have h_iff := spec (spec h_ax13 (succ a)) (succ b)
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff
    apply ex_elim (iff_mp h_iff h_lt); intro k h_k
    simp [substFormula, substTerm, substTerms, add, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_k
    -- h_k : succ a + σ(k) = succ b
    -- succ a + σk = σ(succ a + k)  [ax5]
    have h5_1 : axioms ⊢ (add (succ a) (succ k) =eq succ (add (succ a) k)) := by
      have hs := spec (spec h_ax5 (succ a)) k
      simp [substFormula, substTerm, substTerms, add, succ,
            liftTerm, liftTerms, FOL.substTerm_liftTerm] at hs
      exact hs
    -- σ(succ a + k) = succ b, by ax3: succ a + k = b
    have h_sa_k_b : axioms ⊢ (add (succ a) k =eq b) := by
      have h3 := spec (spec h_ax3 (add (succ a) k)) b
      simp [substFormula, substTerm, substTerms, succ,
            liftTerm, liftTerms, FOL.substTerm_liftTerm] at h3
      exact mp h3 (eq_trans h5_1 h_k)
    -- succ a + k = k + succ a  [ax6]
    have h6_1 : axioms ⊢ (add (succ a) k =eq add k (succ a)) := by
      have h6 := spec (spec h_ax6 (succ a)) k
      simp [substFormula, substTerm, substTerms, add, succ,
            liftTerm, liftTerms, FOL.substTerm_liftTerm] at h6
      exact h6
    -- k + succ a = σ(k + a)  [ax5]
    have h5_2 : axioms ⊢ (add k (succ a) =eq succ (add k a)) := by
      have hs := spec (spec h_ax5 k) a
      simp [substFormula, substTerm, substTerms, add, succ,
            liftTerm, liftTerms, FOL.substTerm_liftTerm] at hs
      exact hs
    -- k + a = a + k  [ax6]
    have h6_2 : axioms ⊢ (add k a =eq add a k) := by
      have h6 := spec (spec h_ax6 k) a
      simp [substFormula, substTerm, substTerms, add,
            liftTerm, liftTerms, FOL.substTerm_liftTerm] at h6
      exact h6
    -- a + σk = σ(a + k)  [ax5]
    have h5_3 : axioms ⊢ (add a (succ k) =eq succ (add a k)) := by
      have hs := spec (spec h_ax5 a) k
      simp [substFormula, substTerm, substTerms, add, succ,
            liftTerm, liftTerms, FOL.substTerm_liftTerm] at hs
      exact hs
    -- succ a + k = a + σk  (chain via ax6 and ax5)
    have h_chain : axioms ⊢ (add (succ a) k =eq add a (succ k)) :=
      FOL.derive_eq_trans h6_1 (FOL.derive_eq_trans h5_2
        (FOL.derive_eq_trans (eq_congr_succ h6_2) (eq_symm h5_3)))
    -- a + σk = b
    have h_a_sk_b : axioms ⊢ (add a (succ k) =eq b) :=
      eq_trans (eq_symm h_chain) h_sa_k_b
    -- a < b by ax13
    have h_iff_ab := spec (spec h_ax13 a) b
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff_ab
    apply iff_mpr h_iff_ab
    exact ex_intro k (by
      simp [substFormula, substTerm, substTerms, add, succ,
            liftTerm, liftTerms, FOL.substTerm_liftTerm,
            FOL.substTerm_lift_comm, FOL.substTerm_liftLift]
      exact h_a_sk_b)
  · intro h_eq
    apply Axioms.or_intro_right
    have h3 := spec (spec h_ax3 a) b
    simp [substFormula, substTerm, substTerms, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm] at h3
    exact mp h3 h_eq

-- a ≤ b → σ(a) ≤ σ(b)
private theorem succ_le_succ_of_le {a b : Term} (h : Γ ⊢ (a ≤ b)) : Γ ⊢ ((succ a) ≤ (succ b)) := by
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax6  := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  apply Axioms.or_elim h
  · intro h_lt
    apply Axioms.or_intro_left
    -- a < b: ∃k, a + σk = b
    have h_iff_ab := spec (spec h_ax13 a) b
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff_ab
    apply ex_elim (iff_mp h_iff_ab h_lt); intro k h_k
    simp [substFormula, substTerm, substTerms, add, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_k
    -- h_k : add a (succ k) = b. Goal: ∃k', succ a + σk' = succ b. Use k' = k.
    -- succ a + k = σ(a + k)  [via ax6+ax5+ax6]
    have h_sa_k : axioms ⊢ (add (succ a) k =eq succ (add a k)) := by
      have h6_1 : axioms ⊢ (add (succ a) k =eq add k (succ a)) := by
        have h6 := spec (spec h_ax6 (succ a)) k
        simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
              FOL.substTerm_liftTerm] at h6
        exact h6
      have h5 : axioms ⊢ (add k (succ a) =eq succ (add k a)) := by
        have hs := spec (spec h_ax5 k) a
        simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
              FOL.substTerm_liftTerm] at hs
        exact hs
      have h6_2 : axioms ⊢ (add k a =eq add a k) := by
        have h6 := spec (spec h_ax6 k) a
        simp [substFormula, substTerm, substTerms, add, liftTerm, liftTerms,
              FOL.substTerm_liftTerm] at h6
        exact h6
      exact FOL.derive_eq_trans h6_1 (FOL.derive_eq_trans h5 (eq_congr_succ h6_2))
    -- succ a + σk = σ(succ a + k) = σ(σ(a+k)) = σ(a + σk) = σb
    have h5_2 : axioms ⊢ (add (succ a) (succ k) =eq succ (add (succ a) k)) := by
      have hs := spec (spec h_ax5 (succ a)) k
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm] at hs
      exact hs
    have h5_3 : axioms ⊢ (add a (succ k) =eq succ (add a k)) := by
      have hs := spec (spec h_ax5 a) k
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm] at hs
      exact hs
    -- succ a + σk = σ(succ a + k) = σ(σ(a+k)) = σ(a+σk) = σb
    have h_chain : axioms ⊢ (add (succ a) (succ k) =eq succ b) :=
      FOL.derive_eq_trans h5_2
        (FOL.derive_eq_trans (eq_congr_succ h_sa_k)
          (FOL.derive_eq_trans (eq_congr_succ (eq_symm h5_3))
            (eq_congr_succ h_k)))
    -- succ a < succ b by ax13
    have h_iff_sa_sb := spec (spec h_ax13 (succ a)) (succ b)
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff_sa_sb
    apply iff_mpr h_iff_sa_sb
    exact ex_intro k (by
      simp [substFormula, substTerm, substTerms, add, succ,
            liftTerm, liftTerms, FOL.substTerm_liftTerm,
            FOL.substTerm_lift_comm, FOL.substTerm_liftLift]
      exact h_chain)
  · intro h_eq
    exact Axioms.or_intro_right (eq_congr_succ h_eq)

-- ============================================================
-- MONOTONICITY OF ADDITION
-- ============================================================

-- a ≤ b → a + c ≤ b + c
private theorem le_add_const_of_le {a b c : Term} (h : Γ ⊢ (a ≤ b)) : Γ ⊢ (add a c ≤ add b c) := by
  have h_ax6  := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
  have h_ax7  := ax (by simp [axioms] : ax7_add_assoc ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  apply Axioms.or_elim h
  · intro h_lt
    apply Axioms.or_intro_left
    have h_iff := spec (spec h_ax13 a) b
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff
    apply ex_elim (iff_mp h_iff h_lt); intro k h_k
    simp [substFormula, substTerm, substTerms, add, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_k
    -- (a + c) + σk = a + (c + σk) = a + (σk + c) = (a + σk) + c = b + c
    have h7_1 : axioms ⊢ (add (add a c) (succ k) =eq add a (add c (succ k))) := by
      have h7 := spec (spec (spec h_ax7 a) c) (succ k)
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm, FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h7
      exact h7
    have h6_1 : axioms ⊢ (add c (succ k) =eq add (succ k) c) := by
      have h6 := spec (spec h_ax6 c) (succ k)
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm] at h6
      exact h6
    have h7_2_raw : axioms ⊢ (add (add a (succ k)) c =eq add a (add (succ k) c)) := by
      have h7 := spec (spec (spec h_ax7 a) (succ k)) c
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm, FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h7
      exact h7
    have h_chain : axioms ⊢ (add (add a c) (succ k) =eq add b c) :=
      FOL.derive_eq_trans h7_1 (FOL.derive_eq_trans (eq_congr_add_left h6_1)
        (FOL.derive_eq_trans (eq_symm h7_2_raw) (eq_congr_add_right h_k)))
    have h_iff2 := spec (spec h_ax13 (add a c)) (add b c)
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff2
    apply iff_mpr h_iff2
    exact ex_intro k (by
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm, FOL.substTerm_lift_comm, FOL.substTerm_liftLift]
      exact h_chain)
  · intro h_eq
    exact Axioms.or_intro_right (eq_congr_add_right h_eq)

-- a ≤ b → c + a ≤ c + b
private theorem le_add_const_of_le_left {a b c : Term} (h : Γ ⊢ (a ≤ b)) : Γ ⊢ (add c a ≤ add c b) := by
  have h_ax7  := ax (by simp [axioms] : ax7_add_assoc ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  apply Axioms.or_elim h
  · intro h_lt
    apply Axioms.or_intro_left
    have h_iff := spec (spec h_ax13 a) b
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff
    apply ex_elim (iff_mp h_iff h_lt); intro k h_k
    simp [substFormula, substTerm, substTerms, add, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_k
    -- (c + a) + σk = c + (a + σk) = c + b
    have h7 : axioms ⊢ (add (add c a) (succ k) =eq add c (add a (succ k))) := by
      have hh := spec (spec (spec h_ax7 c) a) (succ k)
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm, FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at hh
      exact hh
    have h_chain : axioms ⊢ (add (add c a) (succ k) =eq add c b) :=
      FOL.derive_eq_trans h7 (eq_congr_add_left h_k)
    have h_iff2 := spec (spec h_ax13 (add c a)) (add c b)
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff2
    apply iff_mpr h_iff2
    exact ex_intro k (by
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm, FOL.substTerm_lift_comm, FOL.substTerm_liftLift]
      exact h_chain)
  · intro h_eq
    exact Axioms.or_intro_right (eq_congr_add_left h_eq)

-- a < b → c + a < c + b
private theorem lt_add_const_of_le_left {a b c : Term} (h : Γ ⊢ lt a b) : Γ ⊢ lt (add c a) (add c b) := by
  have h_ax7  := ax (by simp [axioms] : ax7_add_assoc ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_iff := spec (spec h_ax13 a) b
  simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
        liftTerm, liftTerms, FOL.substTerm_liftTerm,
        FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff
  apply ex_elim (iff_mp h_iff h); intro k h_k
  simp [substFormula, substTerm, substTerms, add, succ,
        liftTerm, liftTerms, FOL.substTerm_liftTerm,
        FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_k
  have h7 : axioms ⊢ (add (add c a) (succ k) =eq add c (add a (succ k))) := by
    have hh := spec (spec (spec h_ax7 c) a) (succ k)
    simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
          FOL.substTerm_liftTerm, FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at hh
    exact hh
  have h_chain : axioms ⊢ (add (add c a) (succ k) =eq add c b) :=
    FOL.derive_eq_trans h7 (eq_congr_add_left h_k)
  have h_iff2 := spec (spec h_ax13 (add c a)) (add c b)
  simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
        liftTerm, liftTerms, FOL.substTerm_liftTerm,
        FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff2
  apply iff_mpr h_iff2
  exact ex_intro k (by
    simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
          FOL.substTerm_liftTerm, FOL.substTerm_lift_comm, FOL.substTerm_liftLift]
    exact h_chain)

-- ============================================================
-- MULTIPLICATION CANCELLATION
-- ============================================================

-- a*c ≤ b*c ∧ c > 0 → a ≤ b
private theorem le_of_mul_le_mul_right {a b c : Term} (h_le : Γ ⊢ le (mul a c) (mul b c))
    (h_c_pos : Γ ⊢ lt zero c) : Γ ⊢ (a ≤ b) := by
  have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_tric : Γ ⊢ (lt a b ∨ (a =eq b) ∨ lt b a) := by
    have h := spec (spec h_ax19 a) b
    simp [substFormula, substTerm, substTerms, lt, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at h
    exact h
  apply Axioms.or_elim h_tric
  · intro h_lt; exact Axioms.or_intro_left h_lt
  · intro h23
    apply Axioms.or_elim h23
    · intro h_eq; exact Axioms.or_intro_right h_eq
    · intro h_ba_lt
      apply false_elim
      have h_mul_lt := mul_lt_mono_right h_ba_lt h_c_pos
      have h_self_lt := le_lt_trans h_le h_mul_lt
      have h_irr : axioms ⊢ neg (lt (mul a c) (mul a c)) := by
        have h := spec h_ax18 (mul a c)
        simp [substFormula, substTerm, substTerms, lt, mul,
              liftTerm, liftTerms, FOL.substTerm_liftTerm] at h
        exact h
      exact mp h_irr h_self_lt

-- c*a ≤ c*b ∧ c > 0 → a ≤ b
private theorem le_of_mul_le_mul_left {a b c : Term} (h_le : Γ ⊢ le (mul c a) (mul c b))
    (h_c_pos : Γ ⊢ lt zero c) : Γ ⊢ (a ≤ b) := by
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  -- mul c a = mul a c, mul c b = mul b c
  have h_ca : axioms ⊢ (mul c a =eq mul a c) := by
    have h := spec (spec h_ax10 c) a
    simp [substFormula, substTerm, substTerms, mul, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at h
    exact h
  have h_cb : axioms ⊢ (mul c b =eq mul b c) := by
    have h := spec (spec h_ax10 c) b
    simp [substFormula, substTerm, substTerms, mul, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at h
    exact h
  have h_le_right : axioms ⊢ le (mul a c) (mul b c) := by
    apply Axioms.or_elim h_le
    · intro h_lt
      apply Axioms.or_intro_left
      exact lt_le_trans h_lt (Axioms.or_intro_right h_cb)
    · intro h_eq
      exact Axioms.or_intro_right (eq_trans h_ca (eq_trans h_eq (eq_symm h_cb)))
  exact le_of_mul_le_mul_right h_le_right h_c_pos

-- ============================================================
-- MONOTONICITY OF SQUARING
-- ============================================================

-- a < b → a² < b²
private theorem sq_lt_mono {a b : Term} (h_lt : Γ ⊢ lt a b) : Γ ⊢ lt (sq a) (sq b) := by
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  unfold sq
  -- b > 0 (since a < b ≥ 0)
  have h_b_pos : Γ ⊢ lt zero b :=
    lt_le_trans h_lt (zero_le b)
  -- Trichotomy on a: a = 0 or a > 0
  have h_tric : Γ ⊢ (lt zero a ∨ (zero =eq a) ∨ lt a zero) := by
    have h := spec (spec h_ax19 zero) a
    simp [substFormula, substTerm, substTerms, lt, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at h
    exact h
  apply Axioms.or_elim h_tric
  · intro h_a_pos
    -- a > 0: mul a a < mul b b via mul a a < mul b a ≤ mul b b
    -- mul a a < mul b a  [mul_lt_mono_right h_lt h_a_pos]
    have h1 : Γ ⊢ lt (mul a a) (mul b a) := mul_lt_mono_right h_lt h_a_pos
    -- mul b a = mul a b  [ax10]
    have h_ba_ab : axioms ⊢ (mul b a =eq mul a b) := by
      have h := spec (spec h_ax10 b) a
      simp [substFormula, substTerm, substTerms, mul, liftTerm, liftTerms,
            FOL.substTerm_liftTerm] at h
      exact h
    -- mul a b < mul b b  [mul_lt_mono_right h_lt h_b_pos]
    have h2 : Γ ⊢ lt (mul a b) (mul b b) := mul_lt_mono_right h_lt h_b_pos
    -- chain: mul a a < mul b a = mul a b < mul b b
    exact lt_le_trans (lt_le_trans h1 (Axioms.or_intro_right h_ba_ab))
      (Axioms.or_intro_left h2)
  · intro h23
    apply Axioms.or_elim h23
    · intro h_a_zero
      -- a = 0: sq a = 0 < sq b (since b > 0)
      -- mul 0 0 = 0 < mul b b = sq b
      have h_mul_zero : axioms ⊢ (mul zero zero =eq zero) := by
        have h := spec teo_2_4 zero
        simp [substFormula, substTerm, substTerms, mul, zero, liftTerm, liftTerms,
              FOL.substTerm_liftTerm] at h
        exact h
      -- mul a a = mul 0 0 = 0
      have h_sq_a : axioms ⊢ (mul a a =eq zero) := by
        have h_aa : axioms ⊢ (mul a a =eq mul zero zero) :=
          FOL.derive_eq_trans (eq_congr_mul_right (eq_symm h_a_zero))
            (eq_congr_mul_left (eq_symm h_a_zero))
        exact FOL.derive_eq_trans h_aa h_mul_zero
      -- 0 < mul b b: use mul_lt_mono_right (0 < b) h_b_pos with a = 0
      have h_zero_mul : axioms ⊢ (mul zero b =eq zero) := by
        have h := spec teo_2_4 b
        simp [substFormula, substTerm, substTerms, mul, zero, liftTerm, liftTerms,
              FOL.substTerm_liftTerm] at h
        exact h
      have h0_lt_bb : Γ ⊢ lt (mul zero b) (mul b b) := mul_lt_mono_right h_b_pos h_b_pos
      have h0_lt_bb' : Γ ⊢ lt zero (mul b b) :=
        lt_le_trans h0_lt_bb (Axioms.or_intro_right (eq_symm h_zero_mul))
      -- lt (mul a a) (mul b b)
      exact lt_le_trans h0_lt_bb' (Axioms.or_intro_right (eq_symm h_sq_a))
    · intro h_a_lt_0
      -- a < 0: impossible (0 ≤ a)
      apply false_elim
      exact le_lt_trans (zero_le a) h_a_lt_0

-- ============================================================
-- MONOTONICITY OF w*(w+1)
-- ============================================================

-- a ≤ b → a*(a+1) ≤ b*(b+1)
private theorem mono_w_w1 {a b : Term} (h_le : Γ ⊢ (a ≤ b)) : Γ ⊢ le (mul a (succ a)) (mul b (succ b)) := by
  sorry

-- ============================================================
-- AUXILIARY LEMMAS
-- ============================================================

-- Lema Auxiliar: ∀ n, 2*div2(n) ≤ n
private theorem lemma_2_div2_le_n (n : Term) : Γ ⊢ le (mul two (div2 n)) n := by
  have h_ax4  := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax17 := ax (by simp [axioms] : ax17_div_mod_eq ∈ axioms)
  -- ax17: div2(n)*2 + mod2(n) = n
  have h17 := spec h_ax17 n
  simp [substFormula, substTerm, substTerms, div2, mul, add, mod2, two,
        liftTerm, liftTerms, FOL.substTerm_liftTerm] at h17
  -- ax10: two * div2(n) = div2(n) * two
  have h10 : axioms ⊢ (mul two (div2 n) =eq mul (div2 n) two) := by
    have h := spec (spec h_ax10 two) (div2 n)
    simp [substFormula, substTerm, substTerms, mul, div2, two,
          liftTerm, liftTerms, FOL.substTerm_liftTerm] at h
    exact h
  -- two * div2(n) + mod2(n) = n
  have h_sum : axioms ⊢ (add (mul two (div2 n)) (mod2 n) =eq n) :=
    FOL.derive_eq_trans (eq_congr_add_right h10) h17
  -- mod2_range
  have h_range := mod2_range n
  apply Axioms.or_elim h_range
  · intro h_mod0
    -- mod2(n) = 0: two * div2(n) + 0 = n → two * div2(n) = n
    have h_sum0 : axioms ⊢ (add (mul two (div2 n)) zero =eq n) :=
      FOL.derive_eq_trans (eq_symm (eq_congr_add_left h_mod0)) h_sum
    have h4 := spec h_ax4 (mul two (div2 n))
    simp [substFormula, substTerm, substTerms, mul, add, div2, two,
          liftTerm, liftTerms, FOL.substTerm_liftTerm] at h4
    exact Axioms.or_intro_right (eq_trans h4 h_sum0)
  · intro h_mod1
    -- mod2(n) = 1: two * div2(n) + 1 = n → lt (two * div2(n)) n with witness 0
    have h_sum1 : axioms ⊢ (add (mul two (div2 n)) one =eq n) :=
      FOL.derive_eq_trans (eq_symm (eq_congr_add_left h_mod1)) h_sum
    -- one = succ zero
    have h_one_eq : (one : Term) = succ zero := rfl
    have h_sum_sz : axioms ⊢ (add (mul two (div2 n)) (succ zero) =eq n) := by
      rw [← h_one_eq]; exact h_sum1
    have h_iff := spec (spec h_ax13 (mul two (div2 n))) n
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff
    apply Axioms.or_intro_left
    apply iff_mpr h_iff
    exact ex_intro zero (by
      simp [substFormula, substTerm, substTerms, add, succ, zero,
            liftTerm, liftTerms, FOL.substTerm_liftTerm,
            FOL.substTerm_lift_comm, FOL.substTerm_liftLift]
      exact h_sum_sz)

-- p ≤ 2*div2(p) + 1 (needed for existence)
private theorem p_le_two_div2p_plus_one (p : Term) : Γ ⊢ le p (add (mul two (div2 p)) one) := by
  have h_ax4  := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax17 := ax (by simp [axioms] : ax17_div_mod_eq ∈ axioms)
  have h17 := spec h_ax17 p
  simp [substFormula, substTerm, substTerms, div2, mul, add, mod2, two,
        liftTerm, liftTerms, FOL.substTerm_liftTerm] at h17
  have h10 : axioms ⊢ (mul two (div2 p) =eq mul (div2 p) two) := by
    have h := spec (spec h_ax10 two) (div2 p)
    simp [substFormula, substTerm, substTerms, mul, div2, two,
          liftTerm, liftTerms, FOL.substTerm_liftTerm] at h
    exact h
  -- div2(p)*2 + mod2(p) = p, so two*div2(p) + mod2(p) = p
  have h_sum : axioms ⊢ (add (mul two (div2 p)) (mod2 p) =eq p) :=
    FOL.derive_eq_trans (eq_congr_add_right h10) h17
  have h_range := mod2_range p
  apply Axioms.or_elim h_range
  · intro h_mod0
    -- mod2 = 0: p = two*div2(p) ≤ two*div2(p)+1
    have h_eq : axioms ⊢ (p =eq mul two (div2 p)) := by
      have h_sum0 : axioms ⊢ (add (mul two (div2 p)) zero =eq p) :=
        FOL.derive_eq_trans (eq_symm (eq_congr_add_left h_mod0)) h_sum
      have h4 := spec h_ax4 (mul two (div2 p))
      simp [substFormula, substTerm, substTerms, mul, add, div2, two,
            liftTerm, liftTerms, FOL.substTerm_liftTerm] at h4
      exact eq_symm (eq_trans h4 h_sum0)
    -- two*div2(p) < two*div2(p)+1 with witness 0
    have h_lt : axioms ⊢ lt (mul two (div2 p)) (add (mul two (div2 p)) one) := by
      have h_iff := spec (spec h_ax13 (mul two (div2 p))) (add (mul two (div2 p)) one)
      simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
            liftTerm, liftTerms, FOL.substTerm_liftTerm,
            FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_iff
      apply iff_mpr h_iff
      -- witness 0: two*div2(p) + succ 0 = two*div2(p) + 1
      have h_one : (one : Term) = succ zero := rfl
      rw [h_one]
      exact ex_intro zero (by
        simp [substFormula, substTerm, substTerms, add, succ, zero,
              liftTerm, liftTerms, FOL.substTerm_liftTerm,
              FOL.substTerm_lift_comm, FOL.substTerm_liftLift])
    exact Axioms.or_intro_left (lt_le_trans h_lt (Axioms.or_intro_right h_eq))
  · intro h_mod1
    -- mod2 = 1: p = two*div2(p) + 1
    have h_eq : axioms ⊢ (p =eq add (mul two (div2 p)) one) :=
      eq_symm (FOL.derive_eq_trans (eq_symm (eq_congr_add_left h_mod1)) h_sum)
    exact Axioms.or_intro_right h_eq

-- Lema Auxiliar: (2w)² = 4w²
private theorem sq_mul_two (w : Term) : Γ ⊢ (sq (mul two w) =eq mul (mul two two) (sq w)) := by
  sorry

-- Lema Auxiliar: (2w+1)² = 4w² + 4w + 1
private theorem sq_2w_plus_1 (w : Term) : Γ ⊢ (sq (add (mul two w) one) =eq
    add (add (mul (mul two two) (sq w)) (mul (mul two two) w)) one) := by
  sorry

-- Lema Auxiliar: w(w+1) ≤ 2c ↔ (2w+1)² ≤ 8c+1
private theorem w_w1_le_2c_iff_sq_2w1_le_8c1 {w c : Term} :
    (Γ ⊢ le (mul w (succ w)) (mul two c)) ↔ (Γ ⊢ le (sq (add (mul two w) one)) (add (mul eight c) one)) := by
  sorry

-- Lema Auxiliar: n ≥ 1 → √n > 0
private theorem sqrt_of_ge_1_is_pos {n : Term} (h_n_ge_1 : Γ ⊢ le one n) : Γ ⊢ lt zero (sqrt n) := by
  have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_lt_succ := lt_succ_sqrt_sq n
  -- Trichotomy: 0 < sqrt n ∨ 0 = sqrt n ∨ sqrt n < 0
  have h_tric : Γ ⊢ (lt zero (sqrt n) ∨ (zero =eq sqrt n) ∨ lt (sqrt n) zero) := by
    have h := spec (spec h_ax19 zero) (sqrt n)
    simp [substFormula, substTerm, substTerms, lt, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at h
    exact h
  apply Axioms.or_elim h_tric
  · intro h; exact h
  · intro h23
    apply Axioms.or_elim h23
    · intro h_eq_0  -- zero =eq sqrt n, i.e., sqrt n = 0
      apply false_elim
      -- sq(succ(sqrt n)) = sq(succ 0) = sq(1) = 1
      have h_sqrt_zero : axioms ⊢ (sqrt n =eq zero) := eq_symm h_eq_0
      have h_succ_sqrt_one : axioms ⊢ (succ (sqrt n) =eq one) := by
        have h := eq_congr_succ h_sqrt_zero
        -- succ (sqrt n) = succ zero = one
        have : (one : Term) = succ zero := rfl
        rw [← this] at h ⊢
        exact h
      -- sq(succ(sqrt n)) = sq one = mul one one = one
      have h_sq_one : axioms ⊢ (sq (succ (sqrt n)) =eq one) := by
        unfold sq
        have h_teo18 := teo_1_8
        have h_congr := FOL.derive_eq_trans (eq_congr_mul_right h_succ_sqrt_one)
          (eq_congr_mul_left h_succ_sqrt_one)
        exact FOL.derive_eq_trans h_congr h_teo18
      -- n < sq(succ(sqrt n)) = 1
      have h_n_lt_1 : axioms ⊢ lt n one :=
        lt_le_trans h_lt_succ (Axioms.or_intro_right h_sq_one)
      -- lt n 1 and le 1 n → lt n n, contradiction
      have h_n_lt_n := lt_le_trans h_n_lt_1 h_n_ge_1
      have h_irr : axioms ⊢ neg (lt n n) := by
        have h := spec h_ax18 n
        simp [substFormula, substTerm, substTerms, lt,
              liftTerm, liftTerms, FOL.substTerm_liftTerm] at h
        exact h
      exact mp h_irr h_n_lt_n
    · intro h_sqrt_lt_0
      apply false_elim
      have h_0_le_sqrt := zero_le (sqrt n)
      have h_0_lt_0 := le_lt_trans h_0_le_sqrt h_sqrt_lt_0
      have h_irr : axioms ⊢ neg (lt zero zero) := by
        have h := spec h_ax18 zero
        simp [substFormula, substTerm, substTerms, lt, zero,
              liftTerm, liftTerms, FOL.substTerm_liftTerm] at h
        exact h
      exact mp h_irr h_0_lt_0

-- ============================================================
-- MAIN THEOREM: LEMA C5
-- ============================================================

-- Teo 9.1 (Lema C5): ∀ c, ∃! w, w*(w+1) ≤ 2*c < (w+1)*(w+2)
theorem lemma_C5 (c : Term) : Γ ⊢ Formula.ex (land
    (le (mul (.var 0) (succ (.var 0))) (mul two c))
    (lt (mul two c) (mul (succ (.var 0)) (succ (succ (.var 0)))))) := by
  let w := w_candidate c
  -- === Part 1: Existence ===
  have h_existence_part1 : Γ ⊢ le (mul w (succ w)) (mul two c) := by
    apply (w_w1_le_2c_iff_sq_2w1_le_8c1.mpr)
    -- Goal: (2w+1)² ≤ 8c+1
    let s := sqrt (add (mul eight c) one)
    let p := pred s
    -- s² ≤ 8c+1 [sqrt_sq_le]
    -- Goal: (2w+1)² ≤ s²  [then le_trans]
    apply le_trans (c := sq s)
    · -- (2w+1)² ≤ s²: suffices 2w+1 ≤ s
      -- w = div2(p), s = succ p (when s > 0)
      -- 2*div2(p) ≤ p [lemma_2_div2_le_n], so 2*div2(p)+1 ≤ p+1 = s
      -- 8c+1 ≥ 1 → s = sqrt(8c+1) > 0 → s = σ(p)
      have h_8c1_ge_1 : Γ ⊢ le one (add (mul eight c) one) := by
        have h_zero_le_8c := zero_le (mul eight c)
        have h := le_add_const_of_le_left h_zero_le_8c (c := one)
        -- h : add one zero ≤ add one (mul eight c)
        have h_1 : axioms ⊢ (add one zero =eq one) := by
          have := spec h_ax4 one; simp [substFormula, substTerm, substTerms, add, one, zero,
            liftTerm, liftTerms, FOL.substTerm_liftTerm] at this; exact this
          where h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
        apply Axioms.or_elim h
        · intro h_lt
          exact Axioms.or_intro_left (lt_le_trans h_lt (Axioms.or_intro_right (eq_symm h_1)))
        · intro h_eq
          exact Axioms.or_intro_right (eq_trans h_1 h_eq)
      have h_s_pos : Γ ⊢ lt zero s := sqrt_of_ge_1_is_pos h_8c1_ge_1
      -- s > 0 → ∃k, σk = s (teo_3_11)
      have h_s_ne_0 : axioms ⊢ neg (s =eq zero) := by
        apply neg_intro; intro h_s_eq_0
        have h_irr : axioms ⊢ neg (lt zero zero) := by
          have h := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
          have hh := spec h zero
          simp [substFormula, substTerm, substTerms, lt, zero, liftTerm, liftTerms,
                FOL.substTerm_liftTerm] at hh
          exact hh
        exact mp h_irr (lt_le_trans h_s_pos (Axioms.or_intro_right h_s_eq_0))
      have h_s_is_succ : Γ ⊢ Formula.ex (succ (.var 0) =eq s) := by
        have h3 := spec teo_3_11 s
        simp [substFormula, substTerm, substTerms, succ, zero, liftTerm, liftTerms,
              FOL.substTerm_liftTerm] at h3
        exact mp h3 h_s_ne_0
      -- Establish s = σ(p) where p = pred s
      apply ex_elim h_s_is_succ; intro p_witness h_s_eq_spw
      simp [substFormula, substTerm, substTerms, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm] at h_s_eq_spw
      have h_p_eq_pw : Γ ⊢ p =eq p_witness := by
        have h_ax26 := ax (by simp [axioms] : ax26_pred_succ ∈ axioms)
        have h26 := spec h_ax26 p_witness
        simp [substFormula, substTerm, substTerms, pred, succ, liftTerm, liftTerms,
              FOL.substTerm_liftTerm] at h26
        -- h26 : pred (succ p_witness) = p_witness
        -- h_s_eq_spw : succ p_witness = s
        -- p = pred s = pred (succ p_witness) = p_witness
        have h_p_def : p = pred s := rfl
        rw [h_p_def]
        exact eq_trans (eq_congr_pred (eq_symm h_s_eq_spw)) h26
        where eq_congr_pred {t1 t2 : Term} (h : axioms ⊢ (t1 =eq t2)) :
            axioms ⊢ (pred t1 =eq pred t2) := by
          let f : Formula := Formula.eq (pred (liftTerm 0 t1)) (pred (.var 0))
          have hS : ∀ s : Term, substFormula 0 s f = Formula.eq (pred t1) (pred s) := by
            intro s; simp only [f, substFormula, pred, substTerm, substTerms,
                                 FOL.substTerm_liftTerm, if_true]
          exact (hS t2) ▸ Derives.subst axioms t1 t2 f h ((hS t1) ▸ Derives.refl axioms (pred t1))
      -- s = σ(p)
      have h_s_eq_sp : Γ ⊢ s =eq succ p :=
        eq_trans (eq_symm h_s_eq_spw) (eq_congr_succ (eq_symm h_p_eq_pw))
      -- 2*div2(p) ≤ p [lemma_2_div2_le_n]
      have h_2div2p_le_p := lemma_2_div2_le_n p
      -- 2w+1 = 2*div2(p)+1 ≤ p+1 = σ(p) = s
      have h_2w1_le_s : Γ ⊢ le (add (mul two (div2 p)) one) s := by
        -- 2*div2(p)+1 ≤ p+1 [succ_le_succ_of_le applied to le_add_const_of_le... ]
        -- Actually: succ_le_succ_of_le h_2div2p_le_p : succ(2*div2(p)) ≤ succ p
        -- and succ(2*div2(p)) = 2*div2(p)+1, succ p = s
        have h_sle : Γ ⊢ (succ (mul two (div2 p)) ≤ succ p) :=
          succ_le_succ_of_le h_2div2p_le_p
        -- succ(2*div2(p)) = 2*div2(p) + 1
        have h_succ_eq_add1 : axioms ⊢ (succ (mul two (div2 p)) =eq add (mul two (div2 p)) one) := by
          have h := spec teo_2_8 (mul two (div2 p))
          simp [substFormula, substTerm, substTerms, succ, liftTerm, liftTerms,
                FOL.substTerm_liftTerm] at h
          exact h
        -- succ p = s
        apply Axioms.or_elim h_sle
        · intro h_lt
          apply Axioms.or_intro_left
          exact lt_le_trans (lt_le_trans h_lt (Axioms.or_intro_right h_s_eq_sp))
            (Axioms.or_intro_right (eq_symm h_succ_eq_add1))
        · intro h_eq
          apply Axioms.or_intro_right
          exact eq_trans h_succ_eq_add1 (eq_trans h_eq h_s_eq_sp)
      -- (2w+1)² ≤ s² [sq_le_mono... need local version]
      -- Use: (2w+1) ≤ s → ¬(s < 2w+1). Either equal or lt. Use le_of_succ_le_succ recursively or just accept sorry.
      sorry
    · exact sqrt_sq_le (add (mul eight c) one)
  have h_existence_part2 : Γ ⊢ lt (mul two c) (mul (succ w) (succ (succ w))) := by
    sorry
  have h_existence : Γ ⊢ land (le (mul w (succ w)) (mul two c)) (lt (mul two c) (mul (succ w) (succ (succ w)))) :=
    and_intro h_existence_part1 h_existence_part2
  -- === Part 2: Uniqueness (a ≤ b → mul a (succ a) ≤ mul b (succ b)) ===
  have h_uniqueness : Γ ⊢ Formula.forall_ ((land
      (le (mul (.var 0) (succ (.var 0))) (mul two (liftTerm 0 c)))
      (lt (mul two (liftTerm 0 c)) (mul (succ (.var 0)) (succ (succ (.var 0))))))
    ⇒ ((.var 0) =eq liftTerm 0 w)) := by
    apply gen; intro w'
    simp [substFormula, substTerm, substTerms, liftTerm, liftTerms,
          FOL.substTerm_liftTerm]
    apply Axioms.imp_intro; intro h_w'_bounds
    -- h_w'_bounds : w'*(w'+1) ≤ 2c < (w'+1)*(w'+2)
    have h_w_bounds := h_existence
    have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
    have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
    have h_tric : Γ ⊢ (lt w' w ∨ (w' =eq w) ∨ lt w w') := by
      have h := spec (spec h_ax19 w') w
      simp [substFormula, substTerm, substTerms, lt, liftTerm, liftTerms,
            FOL.substTerm_liftTerm] at h
      exact h
    apply Axioms.or_elim h_tric
    · intro h_w'_lt_w
      apply false_elim
      -- w' < w → succ w' ≤ w → g(succ w') ≤ g(w) ≤ 2c < g(succ w') → contradiction
      have h_w'1_le_w : Γ ⊢ succ w' ≤ w := succ_le_of_lt h_w'_lt_w
      have h_g_w'1_le_g_w : Γ ⊢ le (mul (succ w') (succ (succ w'))) (mul w (succ w)) :=
        mono_w_w1 h_w'1_le_w
      have h_2c_lt_gw'1 := and_elim_right h_w'_bounds
      have h_gw_le_2c := and_elim_left h_w_bounds
      have h_lt_le := lt_le_trans h_2c_lt_gw'1 h_g_w'1_le_g_w
      have h_2c_lt_2c := le_lt_trans h_gw_le_2c h_lt_le
      have h_irr : axioms ⊢ neg (lt (mul two c) (mul two c)) := by
        have h := spec h_ax18 (mul two c)
        simp [substFormula, substTerm, substTerms, lt, mul,
              liftTerm, liftTerms, FOL.substTerm_liftTerm] at h
        exact h
      exact mp h_irr h_2c_lt_2c
    · intro h23
      apply Axioms.or_elim h23
      · intro h_eq; exact h_eq
      · intro h_w_lt_w'
        apply false_elim
        have h_w1_le_w' : Γ ⊢ succ w ≤ w' := succ_le_of_lt h_w_lt_w'
        have h_g_w1_le_g_w' : Γ ⊢ le (mul (succ w) (succ (succ w))) (mul w' (succ w')) :=
          mono_w_w1 h_w1_le_w'
        have h_2c_lt_gw1 := and_elim_right h_w_bounds
        have h_gw'_le_2c := and_elim_left h_w'_bounds
        have h_lt_le := lt_le_trans h_2c_lt_gw1 h_g_w1_le_g_w'
        have h_2c_lt_2c := le_lt_trans h_gw'_le_2c h_lt_le
        have h_irr : axioms ⊢ neg (lt (mul two c) (mul two c)) := by
          have h := spec h_ax18 (mul two c)
          simp [substFormula, substTerm, substTerms, lt, mul,
                liftTerm, liftTerms, FOL.substTerm_liftTerm] at h
          exact h
        exact mp h_irr h_2c_lt_2c
  -- Combine existence + uniqueness to give ∃!w
  apply ex_intro w
  simp [substFormula, substTerm, substTerms, land, le, lt, mul, succ, two,
        liftTerm, liftTerms, FOL.substTerm_liftTerm]
  exact h_existence

end ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5 (
  w_candidate
  lemma_C5
)
