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

set_option linter.unusedSimpArgs true

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5

def Γ := axioms

def w_candidate (c : Term) : Term :=
  div2 (pred (sqrt (add (mul eight c) one)))

-- ============================================================
-- BASE HELPERS
-- ============================================================

-- 0 < σ(a): witness a gives 0 + σ(a) = σ(0 + a) = σ(a).
theorem lt_zero_succ (a : Term) : Γ ⊢ lt zero (succ a) := by
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_0sa : axioms ⊢ (add zero (succ a) =eq succ a) := by
    have hs := spec teo_2_2 (succ a)
    simp [substFormula, substTerm, substTerms, add, zero, succ] at hs
    exact hs
  have h_iff := spec (spec h_ax13 zero) (succ a)
  simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
        liftTerm, liftTerms, FOL.substTerm_liftTerm,
        FOL.substTerm_liftLift] at h_iff
  apply iff_mpr h_iff
  exact ex_intro a (by
    simp [substFormula, substTerm, substTerms, FOL.substTerm_liftTerm]
    exact h_0sa)

-- mul_lt_mono_right: a < b → 0 < c → a*c < b*c (re-proof of Block2 private).
theorem mul_lt_mono_right {a b c : Term} (h_lt : Γ ⊢ lt a b) (h_c_pos : Γ ⊢ lt zero c) :
    Γ ⊢ lt (mul a c) (mul b c) := by
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax9  := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_ax12 := ax (by simp [axioms] : ax12_mul_distrib ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  -- Extract kp: a + σ(kp) = b
  have h_iff_ab := spec (spec h_ax13 a) b
  simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_iff_ab
  apply ex_elim (iff_mp h_iff_ab h_lt); intro kp h_kp
  simp [substFormula, substTerm, substTerms, FOL.substTerm_liftTerm] at h_kp
  -- Extract j: 0 + σ(j) = c
  have h_iff_0c := spec (spec h_ax13 zero) c
  simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_iff_0c
  apply ex_elim (iff_mp h_iff_0c h_c_pos); intro j h_j
  simp [substFormula, substTerm, substTerms, zero,
        liftTerm, liftTerms, FOL.substTerm_liftTerm] at h_j
  -- succ j = c  (from 0 + succ j = succ j = c, using teo_2_2)
  have h_0sj : Γ ⊢ (add zero (succ j) =eq succ j) := by
    have hs := spec teo_2_2 (succ j)
    simp [substFormula, substTerm, substTerms, add, zero, succ] at hs
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
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h
    exact h
  have h_comm_ca : Γ ⊢ (mul c a =eq mul a c) := by
    have h := spec (spec h_ax10 c) a
    simp [substFormula, substTerm, substTerms, mul, FOL.substTerm_liftTerm] at h
    exact h
  have h_comm_cskp : Γ ⊢ (mul c (succ kp) =eq mul (succ kp) c) := by
    have h := spec (spec h_ax10 c) (succ kp)
    simp [substFormula, substTerm, substTerms, mul, succ, FOL.substTerm_liftTerm] at h
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
    simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at h
    exact h
  have h_skp_c_succ : Γ ⊢ (mul (succ kp) c =eq succ (add (mul (succ kp) j) kp)) :=
    FOL.derive_eq_trans h_skp_c_sj (FOL.derive_eq_trans h_skp_sj h_add_succ)
  have h_bc_final : Γ ⊢ (mul b c =eq add (mul a c) (succ (add (mul (succ kp) j) kp))) :=
    FOL.derive_eq_trans h_bc_expand (eq_congr_add_left h_skp_c_succ)
  -- lt (mul a c) (mul b c) via ax13
  have h_iff_mac_mbc := spec (spec h_ax13 (mul a c)) (mul b c)
  simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_iff_mac_mbc
  apply iff_mpr h_iff_mac_mbc
  exact ex_intro (add (mul (succ kp) j) kp) (by
    simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm]
    exact eq_symm h_bc_final)

-- ============================================================
-- RING-LIKE HELPERS (object-level commutativity/associativity/distributivity)
-- ============================================================

-- a * b = b * a  [ax10]
theorem mul_comm' (a b : Term) : Γ ⊢ (mul a b =eq mul b a) := by
  have h := spec (spec (ax (by simp [axioms] : ax10_mul_comm ∈ axioms)) a) b
  simp [substFormula, substTerm, substTerms, mul,
        FOL.substTerm_liftTerm] at h
  exact h

-- (a * b) * c = a * (b * c)  [ax11]
theorem mul_assoc' (a b c : Term) : Γ ⊢ (mul (mul a b) c =eq mul a (mul b c)) := by
  have h := spec (spec (spec (ax (by simp [axioms] : ax11_mul_assoc ∈ axioms)) a) b) c
  simp [substFormula, substTerm, substTerms, mul,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h
  exact h

-- a + b = b + a  [ax6]
theorem add_comm' (a b : Term) : Γ ⊢ (add a b =eq add b a) := by
  have h := spec (spec (ax (by simp [axioms] : ax6_add_comm ∈ axioms)) a) b
  simp [substFormula, substTerm, substTerms, add,
        FOL.substTerm_liftTerm] at h
  exact h

-- (a + b) + c = a + (b + c)  [ax7]
theorem add_assoc' (a b c : Term) : Γ ⊢ (add (add a b) c =eq add a (add b c)) := by
  have h := spec (spec (spec (ax (by simp [axioms] : ax7_add_assoc ∈ axioms)) a) b) c
  simp [substFormula, substTerm, substTerms, add,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h
  exact h

-- a * (b + c) = a*b + a*c  [ax12]
theorem mul_distrib' (a b c : Term) :
    Γ ⊢ (mul a (add b c) =eq add (mul a b) (mul a c)) := by
  have h := spec (spec (spec (ax (by simp [axioms] : ax12_mul_distrib ∈ axioms)) a) b) c
  simp [substFormula, substTerm, substTerms, mul, add,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h
  exact h

-- (a + b) * c = a*c + b*c  [right distributivity, via comm]
theorem mul_distrib_right' (a b c : Term) :
    Γ ⊢ (mul (add a b) c =eq add (mul a c) (mul b c)) :=
  FOL.derive_eq_trans (mul_comm' (add a b) c)
    (FOL.derive_eq_trans (mul_distrib' c a b)
      (FOL.derive_eq_trans (eq_congr_add_right (mul_comm' c a))
        (eq_congr_add_left (mul_comm' c b))))

-- ============================================================
-- ORDER LEMMAS FOR SUCCESSOR
-- ============================================================

-- σ(a) ≤ σ(b) → a ≤ b
theorem le_of_succ_le_succ {a b : Term} (h : Γ ⊢ ((succ a) ≤ (succ b))) : Γ ⊢ (a ≤ b) := by
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
          FOL.substTerm_liftLift] at h_iff
    apply ex_elim (iff_mp h_iff h_lt); intro k h_k
    simp [substFormula, substTerm, substTerms, FOL.substTerm_liftTerm] at h_k
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
      simp [substFormula, substTerm, substTerms, succ, FOL.substTerm_liftTerm] at h3
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
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hs
      exact hs
    -- k + a = a + k  [ax6]
    have h6_2 : axioms ⊢ (add k a =eq add a k) := by
      have h6 := spec (spec h_ax6 k) a
      simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftTerm] at h6
      exact h6
    -- a + σk = σ(a + k)  [ax5]
    have h5_3 : axioms ⊢ (add a (succ k) =eq succ (add a k)) := by
      have hs := spec (spec h_ax5 a) k
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hs
      exact hs
    -- succ a + k = a + σk  (chain via ax6 and ax5)
    have h_chain : axioms ⊢ (add (succ a) k =eq add a (succ k)) :=
      FOL.derive_eq_trans h6_1 (FOL.derive_eq_trans h5_2
        (FOL.derive_eq_trans (eq_congr_succ h6_2) (eq_symm h5_3)))
    -- a + σk = b
    have h_a_sk_b : axioms ⊢ (add a (succ k) =eq b) :=
      FOL.derive_eq_trans (eq_symm h_chain) h_sa_k_b
    -- a < b by ax13
    have h_iff_ab := spec (spec h_ax13 a) b
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_iff_ab
    apply iff_mpr h_iff_ab
    exact ex_intro k (by
      simp [substFormula, substTerm, substTerms, FOL.substTerm_liftTerm]
      exact h_a_sk_b)
  · intro h_eq
    apply Axioms.or_intro_right
    have h3 := spec (spec h_ax3 a) b
    simp [substFormula, substTerm, substTerms, succ, FOL.substTerm_liftTerm] at h3
    exact mp h3 h_eq

-- a ≤ b → σ(a) ≤ σ(b)
theorem succ_le_succ_of_le {a b : Term} (h : Γ ⊢ (a ≤ b)) : Γ ⊢ ((succ a) ≤ (succ b)) := by
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax6  := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  apply Axioms.or_elim h
  · intro h_lt
    apply Axioms.or_intro_left
    -- a < b: ∃k, a + σk = b
    have h_iff_ab := spec (spec h_ax13 a) b
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_iff_ab
    apply ex_elim (iff_mp h_iff_ab h_lt); intro k h_k
    simp [substFormula, substTerm, substTerms, FOL.substTerm_liftTerm] at h_k
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
        simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hs
        exact hs
      have h6_2 : axioms ⊢ (add k a =eq add a k) := by
        have h6 := spec (spec h_ax6 k) a
        simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftTerm] at h6
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
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hs
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
          FOL.substTerm_liftLift] at h_iff_sa_sb
    apply iff_mpr h_iff_sa_sb
    exact ex_intro k (by
      simp [substFormula, substTerm, substTerms, FOL.substTerm_liftTerm]
      exact h_chain)
  · intro h_eq
    exact Axioms.or_intro_right (eq_congr_succ h_eq)

-- ============================================================
-- MONOTONICITY OF ADDITION
-- ============================================================

-- a ≤ b → a + c ≤ b + c
theorem le_add_const_of_le {a b c : Term} (h : Γ ⊢ (a ≤ b)) : Γ ⊢ (add a c ≤ add b c) := by
  have h_ax6  := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
  have h_ax7  := ax (by simp [axioms] : ax7_add_assoc ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  apply Axioms.or_elim h
  · intro h_lt
    apply Axioms.or_intro_left
    have h_iff := spec (spec h_ax13 a) b
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_iff
    apply ex_elim (iff_mp h_iff h_lt); intro k h_k
    simp [substFormula, substTerm, substTerms, FOL.substTerm_liftTerm] at h_k
    -- (a + c) + σk = a + (c + σk) = a + (σk + c) = (a + σk) + c = b + c
    have h7_1 : axioms ⊢ (add (add a c) (succ k) =eq add a (add c (succ k))) := by
      have h7 := spec (spec (spec h_ax7 a) c) (succ k)
      simp [substFormula, substTerm, substTerms, add, succ,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h7
      exact h7
    have h6_1 : axioms ⊢ (add c (succ k) =eq add (succ k) c) := by
      have h6 := spec (spec h_ax6 c) (succ k)
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at h6
      exact h6
    have h7_2_raw : axioms ⊢ (add (add a (succ k)) c =eq add a (add (succ k) c)) := by
      have h7 := spec (spec (spec h_ax7 a) (succ k)) c
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h7
      exact h7
    have h_chain : axioms ⊢ (add (add a c) (succ k) =eq add b c) :=
      FOL.derive_eq_trans h7_1 (FOL.derive_eq_trans (eq_congr_add_left h6_1)
        (FOL.derive_eq_trans (eq_symm h7_2_raw) (eq_congr_add_right h_k)))
    have h_iff2 := spec (spec h_ax13 (add a c)) (add b c)
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_iff2
    apply iff_mpr h_iff2
    exact ex_intro k (by
      simp [substFormula, substTerm, substTerms, FOL.substTerm_liftTerm]
      exact h_chain)
  · intro h_eq
    exact Axioms.or_intro_right (eq_congr_add_right h_eq)

-- a ≤ b → c + a ≤ c + b
theorem le_add_const_of_le_left {a b c : Term} (h : Γ ⊢ (a ≤ b)) : Γ ⊢ (add c a ≤ add c b) := by
  have h_ax7  := ax (by simp [axioms] : ax7_add_assoc ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  apply Axioms.or_elim h
  · intro h_lt
    apply Axioms.or_intro_left
    have h_iff := spec (spec h_ax13 a) b
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_iff
    apply ex_elim (iff_mp h_iff h_lt); intro k h_k
    simp [substFormula, substTerm, substTerms, FOL.substTerm_liftTerm] at h_k
    -- (c + a) + σk = c + (a + σk) = c + b
    have h7 : axioms ⊢ (add (add c a) (succ k) =eq add c (add a (succ k))) := by
      have hh := spec (spec (spec h_ax7 c) a) (succ k)
      simp [substFormula, substTerm, substTerms, add, succ,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
      exact hh
    have h_chain : axioms ⊢ (add (add c a) (succ k) =eq add c b) :=
      FOL.derive_eq_trans h7 (eq_congr_add_left h_k)
    have h_iff2 := spec (spec h_ax13 (add c a)) (add c b)
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          liftTerm, liftTerms, FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at h_iff2
    apply iff_mpr h_iff2
    exact ex_intro k (by
      simp [substFormula, substTerm, substTerms, FOL.substTerm_liftTerm]
      exact h_chain)
  · intro h_eq
    exact Axioms.or_intro_right (eq_congr_add_left h_eq)

-- a < b → c + a < c + b
theorem lt_add_const_of_le_left {a b c : Term} (h : Γ ⊢ lt a b) : Γ ⊢ lt (add c a) (add c b) := by
  have h_ax7  := ax (by simp [axioms] : ax7_add_assoc ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_iff := spec (spec h_ax13 a) b
  simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
        FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_iff
  apply ex_elim (iff_mp h_iff h); intro k h_k
  simp [substFormula, substTerm, substTerms,
        FOL.substTerm_liftTerm] at h_k
  have h7 : axioms ⊢ (add (add c a) (succ k) =eq add c (add a (succ k))) := by
    have hh := spec (spec (spec h_ax7 c) a) (succ k)
    simp [substFormula, substTerm, substTerms, add, succ,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
    exact hh
  have h_chain : axioms ⊢ (add (add c a) (succ k) =eq add c b) :=
    FOL.derive_eq_trans h7 (eq_congr_add_left h_k)
  have h_iff2 := spec (spec h_ax13 (add c a)) (add c b)
  simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
        liftTerm, liftTerms, FOL.substTerm_liftTerm,
        FOL.substTerm_liftLift] at h_iff2
  apply iff_mpr h_iff2
  exact ex_intro k (by
    simp [substFormula, substTerm, substTerms,
          FOL.substTerm_liftTerm]
    exact h_chain)

-- ============================================================
-- MULTIPLICATION CANCELLATION
-- ============================================================

-- a*c ≤ b*c ∧ c > 0 → a ≤ b
theorem le_of_mul_le_mul_right {a b c : Term} (h_le : Γ ⊢ le (mul a c) (mul b c))
    (h_c_pos : Γ ⊢ lt zero c) : Γ ⊢ (a ≤ b) := by
  have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_tric : Γ ⊢ (lt a b ∨ (a =eq b) ∨ lt b a) := by
    have h := spec (spec h_ax19 a) b
    simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at h
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
        simp [lt, mul] at h
        exact h
      exact mp h_irr h_self_lt

-- c*a ≤ c*b ∧ c > 0 → a ≤ b
theorem le_of_mul_le_mul_left {a b c : Term} (h_le : Γ ⊢ le (mul c a) (mul c b))
    (h_c_pos : Γ ⊢ lt zero c) : Γ ⊢ (a ≤ b) := by
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  -- mul c a = mul a c, mul c b = mul b c
  have h_ca : axioms ⊢ (mul c a =eq mul a c) := by
    have h := spec (spec h_ax10 c) a
    simp [substFormula, substTerm, substTerms, mul, FOL.substTerm_liftTerm] at h
    exact h
  have h_cb : axioms ⊢ (mul c b =eq mul b c) := by
    have h := spec (spec h_ax10 c) b
    simp [substFormula, substTerm, substTerms, mul, FOL.substTerm_liftTerm] at h
    exact h
  have h_le_right : axioms ⊢ le (mul a c) (mul b c) := by
    apply Axioms.or_elim h_le
    · intro h_lt
      apply Axioms.or_intro_left
      exact lt_le_trans (le_lt_trans (Axioms.or_intro_right (eq_symm h_ca)) h_lt) (Axioms.or_intro_right h_cb)
    · intro h_eq
      exact Axioms.or_intro_right (FOL.derive_eq_trans (FOL.derive_eq_trans (eq_symm h_ca) h_eq) h_cb)
  exact le_of_mul_le_mul_right h_le_right h_c_pos

-- ============================================================
-- MONOTONICITY OF SQUARING
-- ============================================================

-- a < b → a² < b²
theorem sq_lt_mono {a b : Term} (h_lt : Γ ⊢ lt a b) : Γ ⊢ lt (sq a) (sq b) := by
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  unfold sq
  -- b > 0 (since a < b ≥ 0)
  have h_b_pos : Γ ⊢ lt zero b :=
    le_lt_trans (zero_le a) h_lt
  -- Trichotomy on a: a = 0 or a > 0
  have h_tric : Γ ⊢ (lt zero a ∨ (zero =eq a) ∨ lt a zero) := by
    have h := spec (spec h_ax19 zero) a
    simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at h
    exact h
  apply Axioms.or_elim h_tric
  · intro h_a_pos
    -- a > 0: mul a a < mul b b via mul a a < mul b a ≤ mul b b
    -- mul a a < mul b a  [mul_lt_mono_right h_lt h_a_pos]
    have h1 : Γ ⊢ lt (mul a a) (mul b a) := mul_lt_mono_right h_lt h_a_pos
    -- mul b a = mul a b  [ax10]
    have h_ba_ab : axioms ⊢ (mul b a =eq mul a b) := by
      have h := spec (spec h_ax10 b) a
      simp [substFormula, substTerm, substTerms, mul, FOL.substTerm_liftTerm] at h
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
        simp [substFormula, substTerm, substTerms, mul, zero] at h
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
        simp [substFormula, substTerm, substTerms, mul, zero] at h
        exact h
      have h0_lt_bb : Γ ⊢ lt (mul zero b) (mul b b) := mul_lt_mono_right h_b_pos h_b_pos
      have h0_lt_bb' : Γ ⊢ lt zero (mul b b) :=
        le_lt_trans (Axioms.or_intro_right (eq_symm h_zero_mul)) h0_lt_bb
      -- lt (mul a a) (mul b b)
      exact le_lt_trans (Axioms.or_intro_right h_sq_a) h0_lt_bb'
    · intro h_a_lt_0
      -- a < 0: impossible (0 ≤ a)
      have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
      have h_irr : axioms ⊢ neg (lt zero zero) := by
        have h := spec h_ax18 zero
        simp [lt] at h
        exact h
      exact false_elim (mp h_irr (le_lt_trans (zero_le a) h_a_lt_0))

-- ============================================================
-- MONOTONICITY OF w*(w+1)
-- ============================================================

-- a ≤ b → a*c ≤ b*c  (handles c = 0)
theorem le_mul_right {a b c : Term} (h : Γ ⊢ (a ≤ b)) : Γ ⊢ le (mul a c) (mul b c) := by
  have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_tric : Γ ⊢ (lt zero c ∨ (zero =eq c) ∨ lt c zero) := by
    have hh := spec (spec h_ax19 zero) c
    simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at hh
    exact hh
  apply Axioms.or_elim h_tric
  · intro h_c_pos
    apply Axioms.or_elim h
    · intro h_lt; exact Axioms.or_intro_left (mul_lt_mono_right h_lt h_c_pos)
    · intro h_eq; exact Axioms.or_intro_right (eq_congr_mul_right h_eq)
  · intro h23
    apply Axioms.or_elim h23
    · intro h_c0
      apply Axioms.or_intro_right
      have hac : Γ ⊢ (mul a c =eq zero) := by
        have h2 : Γ ⊢ (mul a zero =eq zero) :=
          FOL.derive_eq_trans (mul_comm' a zero) (by
            have hz := spec teo_2_4 a
            simp [substFormula, substTerm, substTerms, mul] at hz
            exact hz)
        exact FOL.derive_eq_trans (eq_congr_mul_left (eq_symm h_c0)) h2
      have hbc : Γ ⊢ (mul b c =eq zero) := by
        have h2 : Γ ⊢ (mul b zero =eq zero) :=
          FOL.derive_eq_trans (mul_comm' b zero) (by
            have hz := spec teo_2_4 b
            simp [substFormula, substTerm, substTerms, mul] at hz
            exact hz)
        exact FOL.derive_eq_trans (eq_congr_mul_left (eq_symm h_c0)) h2
      exact FOL.derive_eq_trans hac (eq_symm hbc)
    · intro h_c_neg
      have h_0lt0 := le_lt_trans (zero_le c) h_c_neg
      have h_irr : axioms ⊢ neg (lt zero zero) := by
        have hh := spec h_ax18 zero
        simp [lt] at hh
        exact hh
      exact false_elim (mp h_irr h_0lt0)

-- x ≤ y → c*x ≤ c*y
theorem le_mul_left {x y c : Term} (h : Γ ⊢ (x ≤ y)) : Γ ⊢ le (mul c x) (mul c y) := by
  have hr : Γ ⊢ le (mul x c) (mul y c) := le_mul_right h
  have hcx : Γ ⊢ (mul c x =eq mul x c) := mul_comm' c x
  have hcy : Γ ⊢ (mul c y =eq mul y c) := mul_comm' c y
  apply Axioms.or_elim hr
  · intro h_lt
    apply Axioms.or_intro_left
    exact lt_le_trans (le_lt_trans (Axioms.or_intro_right hcx) h_lt)
      (Axioms.or_intro_right (eq_symm hcy))
  · intro h_eq
    exact Axioms.or_intro_right
      (FOL.derive_eq_trans (FOL.derive_eq_trans hcx h_eq) (eq_symm hcy))

-- a ≤ b → a*(a+1) ≤ b*(b+1)
theorem mono_w_w1 {a b : Term} (h_le : Γ ⊢ (a ≤ b)) : Γ ⊢ le (mul a (succ a)) (mul b (succ b)) := by
  have h1 : Γ ⊢ le (mul a (succ a)) (mul b (succ a)) := le_mul_right h_le
  have h2 : Γ ⊢ le (mul b (succ a)) (mul b (succ b)) := le_mul_left (succ_le_succ_of_le h_le)
  exact le_trans h1 h2

-- ============================================================
-- AUXILIARY LEMMAS
-- ============================================================

-- Lema Auxiliar: ∀ n, 2*div2(n) ≤ n
theorem lemma_2_div2_le_n (n : Term) : Γ ⊢ le (mul two (div2 n)) n := by
  have h_ax4  := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax17 := ax (by simp [axioms] : ax17_div_mod_eq ∈ axioms)
  -- ax17: div2(n)*2 + mod2(n) = n
  have h17 := spec h_ax17 n
  simp [substFormula, substTerm, substTerms, div2, mul, add, mod2, two] at h17
  -- ax10: two * div2(n) = div2(n) * two
  have h10 : axioms ⊢ (mul two (div2 n) =eq mul (div2 n) two) := by
    have h := spec (spec h_ax10 two) (div2 n)
    simp [substFormula, substTerm, substTerms, mul, div2, two, FOL.substTerm_liftTerm] at h
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
    simp [substFormula, substTerm, substTerms, mul, add, div2, two] at h4
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
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_iff
    apply Axioms.or_intro_left
    apply iff_mpr h_iff
    exact ex_intro zero (by
      simp [substFormula, substTerm, substTerms, zero, FOL.substTerm_liftTerm]
      exact h_sum_sz)

-- p ≤ 2*div2(p) + 1 (needed for existence)
theorem p_le_two_div2p_plus_one (p : Term) : Γ ⊢ le p (add (mul two (div2 p)) one) := by
  have h_ax4  := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax17 := ax (by simp [axioms] : ax17_div_mod_eq ∈ axioms)
  have h17 := spec h_ax17 p
  simp [substFormula, substTerm, substTerms, div2, mul, add, mod2, two] at h17
  have h10 : axioms ⊢ (mul two (div2 p) =eq mul (div2 p) two) := by
    have h := spec (spec h_ax10 two) (div2 p)
    simp [substFormula, substTerm, substTerms, mul, div2, two] at h
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
      simp [substFormula, substTerm, substTerms, mul, add, div2, two] at h4
      exact eq_symm (eq_trans h4 h_sum0)
    -- two*div2(p) < two*div2(p)+1 with witness 0
    have h_lt : axioms ⊢ lt (mul two (div2 p)) (add (mul two (div2 p)) one) := by
      have h_iff := spec (spec h_ax13 (mul two (div2 p))) (add (mul two (div2 p)) one)
      simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
            liftTerm, liftTerms, FOL.substTerm_liftTerm,
            FOL.substTerm_liftLift] at h_iff
      apply iff_mpr h_iff
      -- witness 0: two*div2(p) + succ 0 = two*div2(p) + 1
      have h_one : (one : Term) = succ zero := rfl
      rw [h_one]
      exact ex_intro zero (by
        simp [substFormula, substTerm, substTerms, succ, zero,
              liftTerm, liftTerms, FOL.substTerm_liftTerm]
        exact eq_refl _)
    exact Axioms.or_intro_left (le_lt_trans (Axioms.or_intro_right h_eq) h_lt)
  · intro h_mod1
    -- mod2 = 1: p = two*div2(p) + 1
    have h_eq : axioms ⊢ (p =eq add (mul two (div2 p)) one) :=
      eq_symm (FOL.derive_eq_trans (eq_symm (eq_congr_add_left h_mod1)) h_sum)
    exact Axioms.or_intro_right h_eq

-- Lema Auxiliar: (2w)² = 4w²
theorem sq_mul_two (w : Term) : Γ ⊢ (sq (mul two w) =eq mul (mul two two) (sq w)) := by
  unfold sq
  -- goal: mul (mul two w) (mul two w) =eq mul (mul two two) (mul w w)
  -- (2w)·2 = 2·(w·2) = 2·(2·w) = (2·2)·w
  have step2 : Γ ⊢ (mul (mul two w) two =eq mul (mul two two) w) :=
    FOL.derive_eq_trans (mul_assoc' two w two)
      (FOL.derive_eq_trans (eq_congr_mul_left (mul_comm' w two))
        (eq_symm (mul_assoc' two two w)))
  -- (2w)(2w) = ((2w)·2)·w = ((2·2)·w)·w = (2·2)·(w·w)
  exact FOL.derive_eq_trans (eq_symm (mul_assoc' (mul two w) two w))
    (FOL.derive_eq_trans (eq_congr_mul_right step2)
      (mul_assoc' (mul two two) w w))

-- Lema Auxiliar: (2w+1)² = 4w² + 4w + 1
theorem sq_2w_plus_1 (w : Term) : Γ ⊢ (sq (add (mul two w) one) =eq
    add (add (mul (mul two two) (sq w)) (mul (mul two two) w)) one) := by
  unfold sq
  -- Notation: A := mul two w, X := mul (mul two two) (sq w), M := mul (mul two two) w
  -- Outer distribution: (A+1)(A+1) = (A+1)·A + (A+1)·1
  have hdist := mul_distrib' (add (mul two w) one) (mul two w) one
  -- (A+1)·A = A·A + 1·A
  have hleft := mul_distrib_right' (mul two w) one (mul two w)
  -- (A+1)·1 = A·1 + 1·1
  have hright := mul_distrib_right' (mul two w) one one
  -- A·A = (2·2)·w²
  have hAA : Γ ⊢ (mul (mul two w) (mul two w) =eq mul (mul two two) (sq w)) := sq_mul_two w
  -- 1·A = A
  have h_oneA : Γ ⊢ (mul one (mul two w) =eq mul two w) := by
    have h := spec teo_2_6 (mul two w)
    simp [substFormula, substTerm, substTerms, mul] at h
    exact h
  -- A·1 = A
  have h_Aone : Γ ⊢ (mul (mul two w) one =eq mul two w) := by
    have h := spec teo_2_5 (mul two w)
    simp [substFormula, substTerm, substTerms, mul] at h
    exact h
  -- 1·1 = 1
  have h_oneone : Γ ⊢ (mul one one =eq one) := teo_1_8
  -- 2·A = A + A
  have h_2A : Γ ⊢ (mul two (mul two w) =eq add (mul two w) (mul two w)) := by
    have h := spec teo_2_7 (mul two w)
    simp [substFormula, substTerm, substTerms, mul, add] at h
    exact h
  -- (A+1)·A = (2·2)·w² + A
  have hL : Γ ⊢ (mul (add (mul two w) one) (mul two w) =eq
      add (mul (mul two two) (sq w)) (mul two w)) :=
    FOL.derive_eq_trans hleft
      (FOL.derive_eq_trans (eq_congr_add_right hAA) (eq_congr_add_left h_oneA))
  -- (A+1)·1 = A + 1
  have hR : Γ ⊢ (mul (add (mul two w) one) one =eq add (mul two w) one) :=
    FOL.derive_eq_trans hright
      (FOL.derive_eq_trans (eq_congr_add_right h_Aone) (eq_congr_add_left h_oneone))
  -- (A+1)(A+1) = ((2·2)·w² + A) + (A + 1)
  have hT1 : Γ ⊢ (mul (add (mul two w) one) (add (mul two w) one) =eq
      add (add (mul (mul two two) (sq w)) (mul two w)) (add (mul two w) one)) :=
    FOL.derive_eq_trans hdist
      (FOL.derive_eq_trans (eq_congr_add_right hL) (eq_congr_add_left hR))
  -- Regroup: ((X + A) + (A + 1)) = ((X + M) + 1)
  have hAA_2A : Γ ⊢ (add (mul two w) (mul two w) =eq mul two (mul two w)) := eq_symm h_2A
  have h_2A_M : Γ ⊢ (mul two (mul two w) =eq mul (mul two two) w) :=
    eq_symm (mul_assoc' two two w)
  have hRe : Γ ⊢ (add (add (mul (mul two two) (sq w)) (mul two w)) (add (mul two w) one) =eq
      add (add (mul (mul two two) (sq w)) (mul (mul two two) w)) one) :=
    FOL.derive_eq_trans
      (add_assoc' (mul (mul two two) (sq w)) (mul two w) (add (mul two w) one))
      (FOL.derive_eq_trans
        (eq_congr_add_left (eq_symm (add_assoc' (mul two w) (mul two w) one)))
        (FOL.derive_eq_trans
          (eq_symm (add_assoc' (mul (mul two two) (sq w)) (add (mul two w) (mul two w)) one))
          (FOL.derive_eq_trans
            (eq_congr_add_right (eq_congr_add_left hAA_2A))
            (eq_congr_add_right (eq_congr_add_left h_2A_M)))))
  exact FOL.derive_eq_trans hT1 hRe

-- a ≤ b, a = a', b = b' → a' ≤ b'
theorem le_rewrite {a a' b b' : Term} (h : Γ ⊢ (a ≤ b))
    (ha : Γ ⊢ (a =eq a')) (hb : Γ ⊢ (b =eq b')) : Γ ⊢ (a' ≤ b') := by
  apply Axioms.or_elim h
  · intro h_lt
    exact Axioms.or_intro_left
      (lt_le_trans (le_lt_trans (Axioms.or_intro_right (eq_symm ha)) h_lt)
        (Axioms.or_intro_right hb))
  · intro h_eq
    exact Axioms.or_intro_right
      (FOL.derive_eq_trans (FOL.derive_eq_trans (eq_symm ha) h_eq) hb)

-- a+1 ≤ b+1 → a ≤ b
theorem le_add_one_cancel {x y : Term} (h : Γ ⊢ (add x one ≤ add y one)) : Γ ⊢ (x ≤ y) := by
  have hx : Γ ⊢ (succ x =eq add x one) := by
    have hh := spec teo_2_8 x
    simp [substFormula, substTerm, substTerms, succ, add] at hh
    exact hh
  have hy : Γ ⊢ (succ y =eq add y one) := by
    have hh := spec teo_2_8 y
    simp [substFormula, substTerm, substTerms, succ, add] at hh
    exact hh
  exact le_of_succ_le_succ (le_rewrite h (eq_symm hx) (eq_symm hy))

-- Lema Auxiliar: w(w+1) ≤ 2c ↔ (2w+1)² ≤ 8c+1
theorem w_w1_le_2c_iff_sq_2w1_le_8c1 {w c : Term} :
    (Γ ⊢ le (mul w (succ w)) (mul two c)) ↔ (Γ ⊢ le (sq (add (mul two w) one)) (add (mul eight c) one)) := by
  have h_ax9 := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  -- w(w+1) = w² + w
  have h_wsucc : Γ ⊢ (mul w (succ w) =eq add (sq w) w) := by
    have h := spec (spec h_ax9 w) w
    simp [substFormula, substTerm, substTerms, mul, add, succ, FOL.substTerm_liftTerm] at h
    exact h
  -- 4·w(w+1) = 4w² + 4w
  have E1 : Γ ⊢ (mul (mul two two) (mul w (succ w)) =eq
      add (mul (mul two two) (sq w)) (mul (mul two two) w)) :=
    FOL.derive_eq_trans (eq_congr_mul_left h_wsucc) (mul_distrib' (mul two two) (sq w) w)
  -- 8c = 4·(2c)
  have E2 : Γ ⊢ (mul eight c =eq mul (mul two two) (mul two c)) :=
    FOL.derive_eq_trans (eq_congr_mul_right (eq_symm (mul_assoc' two two two)))
      (mul_assoc' (mul two two) two c)
  -- 0 < 4
  have h_four_pos : Γ ⊢ lt zero (mul two two) :=
    lt_le_trans (lt_zero_succ three) (Axioms.or_intro_right (eq_symm teo_1_10))
  constructor
  · intro h
    have h4 : Γ ⊢ le (mul (mul two two) (mul w (succ w))) (mul (mul two two) (mul two c)) :=
      le_mul_left h
    have h_pq : Γ ⊢ le (add (mul (mul two two) (sq w)) (mul (mul two two) w)) (mul eight c) :=
      le_rewrite h4 E1 (eq_symm E2)
    have h_pq1 : Γ ⊢ le
        (add (add (mul (mul two two) (sq w)) (mul (mul two two) w)) one) (add (mul eight c) one) :=
      le_add_const_of_le h_pq
    exact le_rewrite h_pq1 (eq_symm (sq_2w_plus_1 w)) (eq_refl _)
  · intro h
    have h_pq1 : Γ ⊢ le
        (add (add (mul (mul two two) (sq w)) (mul (mul two two) w)) one) (add (mul eight c) one) :=
      le_rewrite h (sq_2w_plus_1 w) (eq_refl _)
    have h_pq : Γ ⊢ le (add (mul (mul two two) (sq w)) (mul (mul two two) w)) (mul eight c) :=
      le_add_one_cancel h_pq1
    have h4 : Γ ⊢ le (mul (mul two two) (mul w (succ w))) (mul (mul two two) (mul two c)) :=
      le_rewrite h_pq (eq_symm E1) E2
    exact le_of_mul_le_mul_left h4 h_four_pos

-- Lema Auxiliar: n ≥ 1 → √n > 0
theorem sqrt_of_ge_1_is_pos {n : Term} (h_n_ge_1 : Γ ⊢ le one n) : Γ ⊢ lt zero (sqrt n) := by
  have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_lt_succ := lt_succ_sqrt_sq n
  -- Trichotomy: 0 < sqrt n ∨ 0 = sqrt n ∨ sqrt n < 0
  have h_tric : Γ ⊢ (lt zero (sqrt n) ∨ (zero =eq sqrt n) ∨ lt (sqrt n) zero) := by
    have h := spec (spec h_ax19 zero) (sqrt n)
    simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at h
    exact h
  apply Axioms.or_elim h_tric
  · intro h; exact h
  · intro h23
    apply Axioms.or_elim h23
    · intro h_eq_0  -- zero =eq sqrt n, i.e., sqrt n = 0
      apply false_elim
      -- sq(succ(sqrt n)) = sq(succ 0) = sq(1) = 1
      have h_sqrt_zero : axioms ⊢ (sqrt n =eq zero) := eq_symm h_eq_0
      have h_succ_sqrt_one : axioms ⊢ (succ (sqrt n) =eq one) :=
        eq_congr_succ h_sqrt_zero
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
        simp [lt] at h
        exact h
      exact mp h_irr h_n_lt_n
    · intro h_sqrt_lt_0
      apply false_elim
      have h_0_le_sqrt := zero_le (sqrt n)
      have h_0_lt_0 := le_lt_trans h_0_le_sqrt h_sqrt_lt_0
      have h_irr : axioms ⊢ neg (lt zero zero) := by
        have h := spec h_ax18 zero
        simp [lt] at h
        exact h
      exact mp h_irr h_0_lt_0

-- 0 < s → σ(pred s) = s
theorem succ_pred_of_pos {s : Term} (h_pos : Γ ⊢ lt zero s) : Γ ⊢ (succ (pred s) =eq s) := by
  have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
  have h_ax26 := ax (by simp [axioms] : ax26_pred_succ ∈ axioms)
  -- s ≠ 0
  have h_ne : Γ ⊢ neg (s =eq zero) := by
    apply raa; intro h_s0
    have h_lt00 : Γ ⊢ lt zero zero := lt_le_trans h_pos (Axioms.or_intro_right h_s0)
    have h_irr : Γ ⊢ neg (lt zero zero) := by
      have h := spec h_ax18 zero; simp [lt] at h; exact h
    exact mp h_irr h_lt00
  -- ∃ y, σ y = s
  have h_311 := spec teo_3_11 s
  simp [substFormula, substTerm, substTerms, succ, zero] at h_311
  have h_ex := mp h_311 h_ne
  apply ex_elim h_ex; intro y h_y
  simp [substFormula, substTerm, substTerms, FOL.substTerm_liftTerm] at h_y
  -- h_y : σ y = s.  pred s = pred (σ y) = y
  have h_pred_sy : Γ ⊢ (pred s =eq y) := by
    have h26 := spec h_ax26 y
    simp [substFormula, substTerm, substTerms, pred, succ] at h26
    exact FOL.derive_eq_trans (eq_congr_pred (eq_symm h_y)) h26
  exact FOL.derive_eq_trans (eq_congr_succ h_pred_sy) h_y

-- ============================================================
-- MAIN THEOREM: LEMA C5
-- ============================================================

-- Las cotas C5 satisfechas concretamente por `w_candidate c`.
-- Cuerpo extraído de `lemma_C5` para reutilización constructiva en `proj_is_cantor`
-- (Block4_C6_C7), evitando el `ex_elim` que pierde el testigo específico.
theorem c5_bounds (c : Term) :
    Γ ⊢ land (le (mul (w_candidate c) (succ (w_candidate c))) (mul two c))
             (lt (mul two c) (mul (succ (w_candidate c)) (succ (succ (w_candidate c))))) := by
  let w := w_candidate c
  show Γ ⊢ land (le (mul w (succ w)) (mul two c)) (lt (mul two c) (mul (succ w) (succ (succ w))))
  -- === Part 1: Existence ===
  have h_existence_part1 : Γ ⊢ le (mul w (succ w)) (mul two c) := by
    apply (w_w1_le_2c_iff_sq_2w1_le_8c1.mpr)
    -- Goal: (2w+1)² ≤ 8c+1
    let s := sqrt (add (mul eight c) one)
    let p := pred s
    -- s² ≤ 8c+1 [sqrt_sq_le]
    -- Goal: (2w+1)² ≤ s²  [then le_trans]
    have h_sq_s_le_8c1 : Γ ⊢ le (sq s) (add (mul eight c) one) :=
      sqrt_sq_le (add (mul eight c) one)
    have h_sq_2w1_le_sq_s : Γ ⊢ le (sq (add (mul two w) one)) (sq s) := by
      -- 1 ≤ 8c+1
      have h_8c1_ge_1 : Γ ⊢ le one (add (mul eight c) one) :=
        le_rewrite (le_add_const_of_le (zero_le (mul eight c))) teo_1_2 (eq_refl _)
      -- 0 < s
      have h_s_pos : Γ ⊢ lt zero s := sqrt_of_ge_1_is_pos h_8c1_ge_1
      -- (pred s) + 1 = s
      have h_succ_pred_s : Γ ⊢ (succ (pred s) =eq s) := succ_pred_of_pos h_s_pos
      have h_t28 : Γ ⊢ (succ (pred s) =eq add (pred s) one) := by
        have h := spec teo_2_8 (pred s)
        simp [substFormula, substTerm, substTerms, succ, add] at h
        exact h
      have h_p1_eq_s : Γ ⊢ (add (pred s) one =eq s) :=
        FOL.derive_eq_trans (eq_symm h_t28) h_succ_pred_s
      -- 2·div2(p) ≤ p   (p = pred s, w = div2 p)
      have h_2w_le_p : Γ ⊢ le (mul two w) (pred s) := lemma_2_div2_le_n (pred s)
      -- (2w+1) ≤ (pred s)+1 = s
      have h_2w1_le_p1 : Γ ⊢ le (add (mul two w) one) (add (pred s) one) :=
        le_add_const_of_le h_2w_le_p
      have h_2w1_le_s : Γ ⊢ le (add (mul two w) one) s :=
        le_rewrite h_2w1_le_p1 (eq_refl _) h_p1_eq_s
      exact sq_le_mono h_2w1_le_s
    exact le_trans h_sq_2w1_le_sq_s h_sq_s_le_8c1
  have h_existence_part2 : Γ ⊢ lt (mul two c) (mul (succ w) (succ (succ w))) := by
    let s := sqrt (add (mul eight c) one)
    have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
    have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
    -- 2(w+1)+1 = σσ(2w+1)
    have H3 : Γ ⊢ (add (mul two (succ w)) one =eq succ (succ (add (mul two w) one))) := by
      have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
      have h_ax9 := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
      have h9 : Γ ⊢ (mul two (succ w) =eq add (mul two w) two) := by
        have h := spec (spec h_ax9 two) w
        simp [substFormula, substTerm, substTerms, mul, add, succ,
              FOL.substTerm_liftTerm] at h
        exact h
      have h5 : Γ ⊢ (add (mul two w) two =eq succ (add (mul two w) one)) := by
        have h := spec (spec h_ax5 (mul two w)) one
        simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at h
        exact h
      have h28 : Γ ⊢ (succ (succ (add (mul two w) one)) =eq add (succ (add (mul two w) one)) one) := by
        have h := spec teo_2_8 (succ (add (mul two w) one))
        simp [substFormula, substTerm, substTerms, succ, add] at h
        exact h
      exact FOL.derive_eq_trans (eq_congr_add_right (FOL.derive_eq_trans h9 h5)) (eq_symm h28)
    -- 1 ≤ 8c+1, 0 < s, σ(pred s) = s
    have h_8c1_ge_1 : Γ ⊢ le one (add (mul eight c) one) :=
      le_rewrite (le_add_const_of_le (zero_le (mul eight c))) teo_1_2 (eq_refl _)
    have h_s_pos : Γ ⊢ lt zero s := sqrt_of_ge_1_is_pos h_8c1_ge_1
    have h_succ_pred_s : Γ ⊢ (succ (pred s) =eq s) := succ_pred_of_pos h_s_pos
    -- pred s ≤ 2w+1  →  s ≤ σ(2w+1)  →  σs ≤ σσ(2w+1) = 2(w+1)+1
    have h_pred_le : Γ ⊢ le (pred s) (add (mul two w) one) := p_le_two_div2p_plus_one (pred s)
    have h_s_le : Γ ⊢ le s (succ (add (mul two w) one)) :=
      le_rewrite (succ_le_succ_of_le h_pred_le) h_succ_pred_s (eq_refl _)
    have h_ss_le : Γ ⊢ le (succ s) (add (mul two (succ w)) one) :=
      le_rewrite (succ_le_succ_of_le h_s_le) (eq_refl _) (eq_symm H3)
    -- (σs)² ≤ (2(w+1)+1)²,  and  8c+1 < (σs)²
    have h_sq_ss_le : Γ ⊢ le (sq (succ s)) (sq (add (mul two (succ w)) one)) := sq_le_mono h_ss_le
    have h_8c1_lt : Γ ⊢ lt (add (mul eight c) one) (sq (succ s)) :=
      lt_succ_sqrt_sq (add (mul eight c) one)
    have h_upper : Γ ⊢ lt (add (mul eight c) one) (sq (add (mul two (succ w)) one)) :=
      lt_le_trans h_8c1_lt h_sq_ss_le
    -- Trichotomy: if ¬(2c < (w+1)(w+2)) then (w+1)(w+2) ≤ 2c, contradicting via the iff
    have h_irr : Γ ⊢ neg (lt (add (mul eight c) one) (add (mul eight c) one)) := by
      have h := spec h_ax18 (add (mul eight c) one); simp [lt] at h; exact h
    have h_tric : Γ ⊢ (lt (mul two c) (mul (succ w) (succ (succ w))) ∨
        (mul two c =eq mul (succ w) (succ (succ w))) ∨
        lt (mul (succ w) (succ (succ w))) (mul two c)) := by
      have h := spec (spec h_ax19 (mul two c)) (mul (succ w) (succ (succ w)))
      simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at h
      exact h
    apply Axioms.or_elim h_tric
    · intro h_lt; exact h_lt
    · intro h23
      apply Axioms.or_elim h23
      · intro h_eq
        apply false_elim
        have hYle : Γ ⊢ le (mul (succ w) (succ (succ w))) (mul two c) :=
          Axioms.or_intro_right (eq_symm h_eq)
        exact mp h_irr (lt_le_trans h_upper (w_w1_le_2c_iff_sq_2w1_le_8c1.mp hYle))
      · intro h_gt
        apply false_elim
        have hYle : Γ ⊢ le (mul (succ w) (succ (succ w))) (mul two c) :=
          Axioms.or_intro_left h_gt
        exact mp h_irr (lt_le_trans h_upper (w_w1_le_2c_iff_sq_2w1_le_8c1.mp hYle))
  exact Axioms.and_intro h_existence_part1 h_existence_part2

-- Teo 9.1 (Lema C5): ∀ c, ∃ w, w*(w+1) ≤ 2*c < (w+1)*(w+2)
-- Versión existencial: wrapper trivial sobre `c5_bounds` (que da las cotas concretas
-- para `w_candidate c`).
theorem lemma_C5 (c : Term) : Γ ⊢ Formula.ex (land
    (le (mul (.var 0) (succ (.var 0))) (mul two (liftTerm 0 c)))
    (lt (mul two (liftTerm 0 c)) (mul (succ (.var 0)) (succ (succ (.var 0)))))) := by
  apply ex_intro (w_candidate c)
  simp only [substFormula, substTerm, substTerms, land, le, lt, mul, succ,
             FOL.substTerm_liftTerm]
  exact c5_bounds c

-- Unicidad de C5: si w y w' satisfacen las cotas, entonces w = w'.
theorem lemma_C5_unique {c w w' : Term}
    (h_w  : Γ ⊢ land (le (mul w (succ w)) (mul two c))
                     (lt (mul two c) (mul (succ w) (succ (succ w)))))
    (h_w' : Γ ⊢ land (le (mul w' (succ w')) (mul two c))
                     (lt (mul two c) (mul (succ w') (succ (succ w'))))) :
    Γ ⊢ (w =eq w') := by
  have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_w_lo  : Γ ⊢ le (mul w (succ w)) (mul two c) := Axioms.and_elim_left h_w
  have h_w_hi  : Γ ⊢ lt (mul two c) (mul (succ w) (succ (succ w))) := Axioms.and_elim_right h_w
  have h_w'_lo : Γ ⊢ le (mul w' (succ w')) (mul two c) := Axioms.and_elim_left h_w'
  have h_w'_hi : Γ ⊢ lt (mul two c) (mul (succ w') (succ (succ w'))) := Axioms.and_elim_right h_w'
  have h_tric : Γ ⊢ (lt w w' ∨ (w =eq w') ∨ lt w' w) := by
    have h := spec (spec h_ax19 w) w'
    simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at h
    exact h
  apply Axioms.or_elim h_tric
  · intro h_lt
    apply false_elim
    have h_mono : Γ ⊢ le (mul (succ w) (succ (succ w))) (mul w' (succ w')) :=
      mono_w_w1 (succ_le_of_lt h_lt)
    have h_chain : Γ ⊢ lt (mul (succ w) (succ (succ w))) (mul (succ w) (succ (succ w))) :=
      le_lt_trans (le_trans h_mono h_w'_lo) h_w_hi
    have h_irr : Γ ⊢ neg (lt (mul (succ w) (succ (succ w))) (mul (succ w) (succ (succ w)))) := by
      have h := spec h_ax18 (mul (succ w) (succ (succ w))); simp [lt] at h; exact h
    exact mp h_irr h_chain
  · intro h23
    apply Axioms.or_elim h23
    · intro h_eq; exact h_eq
    · intro h_lt
      apply false_elim
      have h_mono : Γ ⊢ le (mul (succ w') (succ (succ w'))) (mul w (succ w)) :=
        mono_w_w1 (succ_le_of_lt h_lt)
      have h_chain : Γ ⊢ lt (mul (succ w') (succ (succ w'))) (mul (succ w') (succ (succ w'))) :=
        le_lt_trans (le_trans h_mono h_w_lo) h_w'_hi
      have h_irr : Γ ⊢ neg (lt (mul (succ w') (succ (succ w'))) (mul (succ w') (succ (succ w')))) := by
        have h := spec h_ax18 (mul (succ w') (succ (succ w'))); simp [lt] at h; exact h
      exact mp h_irr h_chain

-- a ≤ a + b
theorem le_self_add (a b : Term) : Γ ⊢ le a (add a b) := by
  have h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h0 : Γ ⊢ le (add a zero) (add a b) := le_add_const_of_le_left (zero_le b)
  have h4 : Γ ⊢ (add a zero =eq a) := by
    have h := spec h_ax4 a
    simp [substFormula, substTerm, substTerms, add] at h
    exact h
  exact le_rewrite h0 h4 (eq_refl _)

-- lt a b, a = a', b = b' → lt a' b'
theorem lt_rewrite {a a' b b' : Term} (h : Γ ⊢ lt a b)
    (ha : Γ ⊢ (a =eq a')) (hb : Γ ⊢ (b =eq b')) : Γ ⊢ lt a' b' :=
  lt_le_trans (le_lt_trans (Axioms.or_intro_right (eq_symm ha)) h) (Axioms.or_intro_right hb)

-- (w+1)(w+2) = w(w+1) + 2(w+1)
theorem expand_succ_succ (w : Term) :
    Γ ⊢ (mul (succ w) (succ (succ w)) =eq add (mul w (succ w)) (mul two (succ w))) := by
  have h_ax9 := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  have e1 : Γ ⊢ (mul (succ w) (succ (succ w)) =eq add (mul (succ w) (succ w)) (succ w)) := by
    have h := spec (spec h_ax9 (succ w)) (succ w)
    simp [substFormula, substTerm, substTerms, mul, add, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm] at h
    exact h
  have e2 : Γ ⊢ (mul (succ w) (succ w) =eq add (mul (succ w) w) (succ w)) := by
    have h := spec (spec h_ax9 (succ w)) w
    simp [substFormula, substTerm, substTerms, mul, add, succ,
          liftTerm, liftTerms, FOL.substTerm_liftTerm] at h
    exact h
  have e3 : Γ ⊢ (mul (succ w) w =eq mul w (succ w)) := mul_comm' (succ w) w
  have e4 : Γ ⊢ (add (succ w) (succ w) =eq mul two (succ w)) := by
    have h := spec teo_2_7 (succ w)
    simp [substFormula, substTerm, substTerms, mul, add, succ] at h
    exact eq_symm h
  have e12 : Γ ⊢ (mul (succ w) (succ (succ w)) =eq
      add (add (mul w (succ w)) (succ w)) (succ w)) :=
    FOL.derive_eq_trans e1
      (eq_congr_add_right (FOL.derive_eq_trans e2 (eq_congr_add_right e3)))
  have e5 : Γ ⊢ (add (add (mul w (succ w)) (succ w)) (succ w) =eq
      add (mul w (succ w)) (add (succ w) (succ w))) := add_assoc' (mul w (succ w)) (succ w) (succ w)
  exact FOL.derive_eq_trans e12 (FOL.derive_eq_trans e5 (eq_congr_add_left e4))

-- Las cotas C5 para w = x+y, dadas por la ecuación de Cantor 2c = w(w+1) + 2y.
theorem cantor_bounds {x y c : Term}
    (h : Γ ⊢ (mul two c =eq add (mul (add x y) (succ (add x y))) (mul two y))) :
    Γ ⊢ land (le (mul (add x y) (succ (add x y))) (mul two c))
             (lt (mul two c) (mul (succ (add x y)) (succ (succ (add x y))))) := by
  have h_ax9 := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  -- Lower bound: w(w+1) ≤ w(w+1)+2y = 2c
  have h_low : Γ ⊢ le (mul (add x y) (succ (add x y))) (mul two c) :=
    le_rewrite (le_self_add (mul (add x y) (succ (add x y))) (mul two y)) (eq_refl _) (eq_symm h)
  -- y ≤ x+y
  have h_y_le_w : Γ ⊢ le y (add x y) :=
    le_rewrite (le_self_add y x) (eq_refl _) (add_comm' y x)
  have h_2y_le_2w : Γ ⊢ le (mul two y) (mul two (add x y)) := le_mul_left h_y_le_w
  have h_add_le : Γ ⊢ le (add (mul (add x y) (succ (add x y))) (mul two y))
      (add (mul (add x y) (succ (add x y))) (mul two (add x y))) :=
    le_add_const_of_le_left h_2y_le_2w
  -- 2w < 2(w+1)
  have h_2w_lt : Γ ⊢ lt (mul two (add x y)) (mul two (succ (add x y))) := by
    have h9 : Γ ⊢ (mul two (succ (add x y)) =eq add (mul two (add x y)) two) := by
      have hh := spec (spec h_ax9 two) (add x y)
      simp [substFormula, substTerm, substTerms, mul, add, succ,
            FOL.substTerm_liftTerm] at hh
      exact hh
    have hlt : Γ ⊢ lt (mul two (add x y)) (add (mul two (add x y)) two) := by
      have h_iff := spec (spec h_ax13 (mul two (add x y))) (add (mul two (add x y)) two)
      simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
            liftTerm, liftTerms, FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_iff
      apply iff_mpr h_iff
      exact ex_intro one (by
        simp [substFormula, substTerm, substTerms, succ, one, two,
              liftTerm, liftTerms, FOL.substTerm_liftTerm]
        exact eq_refl _)
    exact lt_rewrite hlt (eq_refl _) (eq_symm h9)
  have h_lt2 : Γ ⊢ lt (add (mul (add x y) (succ (add x y))) (mul two (add x y)))
      (add (mul (add x y) (succ (add x y))) (mul two (succ (add x y)))) :=
    lt_add_const_of_le_left h_2w_lt
  have h_expand : Γ ⊢ (mul (succ (add x y)) (succ (succ (add x y))) =eq
      add (mul (add x y) (succ (add x y))) (mul two (succ (add x y)))) := expand_succ_succ (add x y)
  have h_high : Γ ⊢ lt (mul two c) (mul (succ (add x y)) (succ (succ (add x y)))) :=
    lt_rewrite (le_lt_trans h_add_le h_lt2) (eq_symm h) (eq_symm h_expand)
  exact Axioms.and_intro h_low h_high

end ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5 (
  -- main theorems
  w_candidate
  c5_bounds
  lemma_C5
  lemma_C5_unique
  cantor_bounds
  -- reusable order helpers
  le_rewrite
  lt_rewrite
  le_self_add
  le_add_one_cancel
  le_add_const_of_le
  le_add_const_of_le_left
  lt_add_const_of_le_left
  lt_zero_succ
  le_of_succ_le_succ
  succ_le_succ_of_le
  succ_pred_of_pos
  -- reusable arithmetic helpers
  mul_lt_mono_right
  le_mul_right
  le_mul_left
  le_of_mul_le_mul_right
  le_of_mul_le_mul_left
  sq_lt_mono
  -- reusable ring algebra helpers
  add_comm'
  add_assoc'
  mul_comm'
  mul_assoc'
  mul_distrib'
  mul_distrib_right'
)
