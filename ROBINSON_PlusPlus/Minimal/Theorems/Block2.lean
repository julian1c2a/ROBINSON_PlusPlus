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
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block2

set_option linter.unusedSimpArgs false

/-!
## BLOQUE II — RAÍZ CUADRADA
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 4: Cotas y Unicidad de √
-/

-- Teo 4.1: ∀ n, (√n)² ≤ n
theorem sqrt_sq_le (n : Term) : Γ ⊢ ((sq (sqrt n)) ≤ n) := by
  have h_ax14 := ax (by simp [axioms] : ax14_sqrt_le ∈ axioms)
  have h := spec h_ax14 n
  simp only [substFormula, substTerm, substTerms, le, lt, sq, mul, if_true] at h
  exact h

-- Teo 4.2: ∀ n, n < (σ(√n))²
theorem lt_succ_sqrt_sq (n : Term) : Γ ⊢ lt n (sq (succ (sqrt n))) := by
  have h_ax15 := ax (by simp [axioms] : ax15_lt_succ_sqrt ∈ axioms)
  have h := spec h_ax15 n
  simp only [substFormula, substTerm, substTerms, lt, sq, succ, mul, if_true] at h
  exact h

-- Teo 4.3: n² = 0 ⇒ n = 0
theorem sq_eq_zero_imp_zero (n : Term) : Γ ⊢ ((sq n =eq zero) ⇒ (n =eq zero)) := by
  apply Axioms.imp_intro; intro h_sq0
  have h_teo210_inst : Γ ⊢ ((mul n n =eq zero) ⇒ lor (n =eq zero) (n =eq zero)) := by
    have h := spec (spec teo_2_10 n) n
    simp [substFormula, substTerm, substTerms, mul, lor,
          FOL.substTerm_liftTerm] at h
    exact h
  have h_or := mp h_teo210_inst h_sq0
  apply Axioms.or_elim h_or
  · intro h; exact h
  · intro h; exact h

-- Teorema (antes Ax 22): a < b ⇒ σ(a) ≤ b
theorem succ_le_of_lt {a b : Term} (h_lt : Γ ⊢ lt a b) : Γ ⊢ ((succ a) ≤ b) := by
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_tric : Γ ⊢ (lt (succ a) b ∨ (succ a =eq b) ∨ lt b (succ a)) := by
    have h := spec (spec h_ax19 (succ a)) b
    simp [substFormula, substTerm, substTerms,
          liftTerm, liftTerms, lt, succ, FOL.substTerm_liftTerm] at h
    exact h
  apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_tric
  · intro h1; exact ROBINSON_PlusPlus.Minimal.Axioms.or_intro_left h1
  · intro h23
    apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h23
    · intro h2; exact ROBINSON_PlusPlus.Minimal.Axioms.or_intro_right h2
    · intro h_blt_sa
      apply false_elim
      -- Goal: axioms ⊢ ⊥
      have h_ax2  := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
      have h_ax3  := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
      have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
      have h_ax6  := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
      have h_ax7  := ax (by simp [axioms] : ax7_add_assoc ∈ axioms)
      have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
      have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
      -- Extract kp: ∃kp, a + σ(kp) = b
      have h_kp_iff := spec (spec h_ax13 a) b
      simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
            FOL.substTerm_liftTerm,
            FOL.substTerm_liftLift] at h_kp_iff
      apply ex_elim (iff_mp h_kp_iff h_lt)
      intro kp h_kp
      simp [substFormula, substTerm, substTerms,
            FOL.substTerm_liftTerm
            ] at h_kp
      -- Extract k: ∃k, b + σ(k) = σ(a)
      have h_k_iff := spec (spec h_ax13 b) (succ a)
      simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
            liftTerm, liftTerms, FOL.substTerm_liftTerm,
            FOL.substTerm_liftLift] at h_k_iff
      apply ex_elim (iff_mp h_k_iff h_blt_sa)
      intro k h_k
      simp [substFormula, substTerm, substTerms,
            FOL.substTerm_liftTerm
            ] at h_k
      -- h_kp : a + σ(kp) = b,  h_k : b + σ(k) = σ(a)
      -- (a + σ(kp)) + σ(k) = σ(a)
      have h_sub : axioms ⊢ (add (add a (succ kp)) (succ k) =eq succ a) :=
        eq_trans (eq_congr_add_right (eq_symm h_kp)) h_k
      have h_ax7_inst : axioms ⊢ (add (add a (succ kp)) (succ k) =eq add a (add (succ kp) (succ k))) := by
        have ha := spec (spec (spec h_ax7 a) (succ kp)) (succ k)
        simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
              FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at ha
        exact ha
      have h_mid : axioms ⊢ (add a (add (succ kp) (succ k)) =eq succ a) :=
        eq_trans h_ax7_inst h_sub
      have h_ax5_inst : axioms ⊢ (add (succ kp) (succ k) =eq succ (add (succ kp) k)) := by
        have hs := spec (spec h_ax5 (succ kp)) k
        simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
              FOL.substTerm_liftTerm] at hs
        exact hs
      have h_mid2 : axioms ⊢ (add a (succ (add (succ kp) k)) =eq succ a) :=
        eq_trans (eq_congr_add_left h_ax5_inst) h_mid
      have h_sa_eq : axioms ⊢ (succ a =eq add a one) := by
        have hs := spec teo_2_8 a
        simp [substFormula, substTerm, substTerms, succ
              ] at hs
        exact hs
      -- a + σ(σ(kp)+k) = a + 1
      have h_mid3 : axioms ⊢ (add a (succ (add (succ kp) k)) =eq add a one) :=
        eq_trans (eq_symm h_mid2) h_sa_eq
      -- Refactor 2026-06-03 (sin ax27): usa ax13+ax3+ax18 vía la identidad
      -- "no hay X tal que a + σX = a". Esquema:
      --   a + σ(σkp+k) = a + 1 = succ a
      --   ⇒ succ(a + (σkp+k)) = succ a       (ax5 izq)
      --   ⇒ a + (σkp+k) = a                  (ax3 inj)
      --   ⇒ a + σ(k+kp) = a                  (ax6+ax5 reescribiendo σkp+k)
      --   pero ax13 da lt a (a + σ(k+kp)) con testigo k+kp
      --   ⇒ lt a a, contradice ax18.
      -- LHS = succ(a + (σkp+k))  vía ax5
      have h_LHS_eq : axioms ⊢
          (add a (succ (add (succ kp) k)) =eq succ (add a (add (succ kp) k))) := by
        have hh := spec (spec h_ax5 a) (add (succ kp) k)
        simp [substFormula, substTerm, substTerms, add, succ,
              FOL.substTerm_liftTerm] at hh
        exact hh
      -- RHS = succ a  vía ax5 (a + σ0 = σ(a+0)) + ax4 (a+0=a); usamos `one = σ zero`
      have h_RHS_eq : axioms ⊢ (add a one =eq succ a) := by
        have h5 := spec (spec h_ax5 a) zero
        simp [substFormula, substTerm, substTerms, add, succ, zero,
              FOL.substTerm_liftTerm] at h5
        -- h5 : a + succ zero =eq succ (a + zero), i.e., a + one = succ (a + zero)
        have h_ax4 := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
        have h4 : axioms ⊢ (add a zero =eq a) := by
          have hh := spec h_ax4 a
          simp [substFormula, substTerm, substTerms, add, zero] at hh
          exact hh
        exact FOL.derive_eq_trans h5 (eq_congr_succ h4)
      -- succ(a + (σkp+k)) = succ a
      have h_succ_eq : axioms ⊢ (succ (add a (add (succ kp) k)) =eq succ a) :=
        FOL.derive_eq_trans (eq_symm h_LHS_eq) (FOL.derive_eq_trans h_mid3 h_RHS_eq)
      -- ax3 inj: a + (σkp+k) = a
      have h_a_X_eq_a : axioms ⊢ (add a (add (succ kp) k) =eq a) := by
        have hw := spec (spec h_ax3 (add a (add (succ kp) k))) a
        simp [substFormula, substTerm, substTerms, succ,
              FOL.substTerm_liftTerm] at hw
        exact mp hw h_succ_eq
      -- Reescribir σkp + k = σ(k + kp)  vía ax6 + ax5
      have h_comm_kp_k : axioms ⊢ (add (succ kp) k =eq add k (succ kp)) := by
        have hc := spec (spec h_ax6 (succ kp)) k
        simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
              FOL.substTerm_liftTerm] at hc
        exact hc
      have h_ax5_k_kp : axioms ⊢ (add k (succ kp) =eq succ (add k kp)) := by
        have hh := spec (spec h_ax5 k) kp
        simp [substFormula, substTerm, substTerms, add, succ,
              FOL.substTerm_liftTerm] at hh
        exact hh
      have h_inner_eq : axioms ⊢ (add (succ kp) k =eq succ (add k kp)) :=
        FOL.derive_eq_trans h_comm_kp_k h_ax5_k_kp
      -- a + σ(k+kp) = a
      have h_a_plus_succ_eq_a : axioms ⊢ (add a (succ (add k kp)) =eq a) :=
        FOL.derive_eq_trans (eq_congr_add_left (eq_symm h_inner_eq)) h_a_X_eq_a
      -- ax13: lt a (a + σ(k+kp))  con testigo (k+kp)
      have h_lt_a_aX : axioms ⊢ lt a (add a (succ (add k kp))) := by
        have h_iff := spec (spec h_ax13 a) (add a (succ (add k kp)))
        simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
              liftTerm, liftTerms, FOL.substTerm_liftTerm,
              FOL.substTerm_liftLift] at h_iff
        apply iff_mpr h_iff
        apply ex_intro (add k kp)
        simp [substFormula, substTerm, substTerms, add,
              FOL.substTerm_liftTerm]
        exact eq_refl _
      -- Sustituir (a + σ(k+kp)) → a   vía Derives.subst
      let f_lt_a : Formula := Formula.atom lt_sym [liftTerm 0 a, .var 0]
      have hS_aX : substFormula 0 (add a (succ (add k kp))) f_lt_a
          = lt a (add a (succ (add k kp))) := by
        simp only [f_lt_a, substFormula, substTerm, substTerms, lt,
                   FOL.substTerm_liftTerm, if_true]
      have hS_a : substFormula 0 a f_lt_a = lt a a := by
        simp only [f_lt_a, substFormula, substTerm, substTerms, lt,
                   FOL.substTerm_liftTerm, if_true]
      have h_lt_aa : axioms ⊢ lt a a :=
        hS_a ▸ Derives.subst axioms (add a (succ (add k kp))) a f_lt_a
              h_a_plus_succ_eq_a (hS_aX ▸ h_lt_a_aX)
      -- Contradicción con ax18 (irreflexividad)
      have h_irr_a : axioms ⊢ neg (lt a a) := by
        have hh := spec h_ax18 a
        simp [lt] at hh
        exact hh
      exact mp h_irr_a h_lt_aa

-- Lema Auxiliar: ∀ n, 0 ≤ n
theorem zero_le (n : Term) : Γ ⊢ (zero ≤ n) := by
  have h_ax2  := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_tric : Γ ⊢ (lt zero n ∨ (zero =eq n) ∨ lt n zero) := by
    have h := spec (spec h_ax19 zero) n
    simp [substFormula, substTerm, substTerms, lt,
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
      simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms,
            FOL.substTerm_liftTerm] at hh
      apply ex_elim (iff_mp hh h_nlt0)
      intro k h_k
      simp [substFormula, substTerm, substTerms,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_k
      have h_step : Γ ⊢ (add n (succ k) =eq succ (add n k)) := by
        have hs := spec (spec h_ax5 n) k
        simp [substFormula, substTerm, substTerms, add, succ,
              FOL.substTerm_liftTerm] at hs
        exact hs
      have h_neq0 : Γ ⊢ neg (succ (add n k) =eq zero) := by
        have hn := spec h_ax2 (add n k)
        simp [succ
              ] at hn
        exact hn
      exact mp h_neq0 (eq_trans h_step h_k)

-- Lemas auxiliares de transitividad
theorem lt_le_trans {a b c : Term} (h_lt : Γ ⊢ lt a b) (h_le : Γ ⊢ (b ≤ c)) : Γ ⊢ lt a c := by
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have ex_to_lt_ac : (∃ k : Term, Γ ⊢ (add a (succ k) =eq c)) → Γ ⊢ lt a c := by
    intro ⟨k, h_k⟩
    have h_iff := by
      have h := spec (spec h_ax13 a) c
      simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
            FOL.substTerm_liftTerm,
            FOL.substTerm_liftLift] at h
      exact h
    apply iff_mpr h_iff
    exact ex_intro k (by
      simp [substFormula, substTerm, substTerms,
            FOL.substTerm_liftTerm]
      exact h_k)
  apply Axioms.or_elim h_le
  · intro h_lt_bc
    -- Get iff for lt a b, apply ex_elim to get j
    have h_iff_ab := spec (spec h_ax13 a) b
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at h_iff_ab
    -- Get iff for lt b c, apply ex_elim to get k
    have h_iff_bc := spec (spec h_ax13 b) c
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at h_iff_bc
    apply ex_elim (iff_mp h_iff_ab h_lt)
    intro j h_j_raw
    simp [substFormula, substTerm, substTerms,
          FOL.substTerm_liftTerm
          ] at h_j_raw
    apply ex_elim (iff_mp h_iff_bc h_lt_bc)
    intro k h_k_raw
    simp [substFormula, substTerm, substTerms,
          FOL.substTerm_liftTerm
          ] at h_k_raw
    -- h_j_raw: add a (succ j) = b,  h_k_raw: add b (succ k) = c
    have h_sub : Γ ⊢ (add (add a (succ j)) (succ k) =eq c) :=
      eq_trans (eq_congr_add_right (eq_symm h_j_raw)) h_k_raw
    have h_ax7 := ax (by simp [axioms] : ax7_add_assoc ∈ axioms)
    have h_assoc : Γ ⊢ (add (add a (succ j)) (succ k) =eq add a (add (succ j) (succ k))) := by
      have ha := spec (spec (spec h_ax7 a) (succ j)) (succ k)
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at ha
      exact ha
    have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
    have h_ax5_inst : Γ ⊢ (add (succ j) (succ k) =eq succ (add (succ j) k)) := by
      have hs := spec (spec h_ax5 (succ j)) k
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm] at hs
      exact hs
    have h_wit : Γ ⊢ (add a (succ (add (succ j) k)) =eq c) :=
      eq_trans (eq_congr_add_left h_ax5_inst) (eq_trans h_assoc h_sub)
    exact ex_to_lt_ac ⟨add (succ j) k, h_wit⟩
  · intro h_eq_bc
    have h_iff_ab := spec (spec h_ax13 a) b
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at h_iff_ab
    apply ex_elim (iff_mp h_iff_ab h_lt)
    intro j h_j_raw
    simp [substFormula, substTerm, substTerms,
          FOL.substTerm_liftTerm
          ] at h_j_raw
    exact ex_to_lt_ac ⟨j, FOL.derive_eq_trans h_j_raw h_eq_bc⟩

theorem le_lt_trans {a b c : Term} (h_le : Γ ⊢ (a ≤ b)) (h_lt : Γ ⊢ lt b c) : Γ ⊢ lt a c := by
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have ex_to_lt_ac : (∃ k : Term, Γ ⊢ (add a (succ k) =eq c)) → Γ ⊢ lt a c := by
    intro ⟨k, h_k⟩
    have h_iff := by
      have h := spec (spec h_ax13 a) c
      simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
            FOL.substTerm_liftTerm,
            FOL.substTerm_liftLift] at h
      exact h
    apply iff_mpr h_iff
    exact ex_intro k (by
      simp [substFormula, substTerm, substTerms,
            FOL.substTerm_liftTerm]
      exact h_k)
  apply Axioms.or_elim h_le
  · intro h_lt_ab
    exact lt_le_trans h_lt_ab (Axioms.or_intro_left h_lt)
  · intro h_eq_ab
    have h_iff_bc := spec (spec h_ax13 b) c
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at h_iff_bc
    apply ex_elim (iff_mp h_iff_bc h_lt)
    intro k h_k_raw
    simp [substFormula, substTerm, substTerms,
          FOL.substTerm_liftTerm
          ] at h_k_raw
    exact ex_to_lt_ac ⟨k, FOL.derive_eq_trans (eq_congr_add_right h_eq_ab) h_k_raw⟩

theorem le_trans {a b c : Term} (h_ab : Γ ⊢ (a ≤ b)) (h_bc : Γ ⊢ (b ≤ c)) : Γ ⊢ (a ≤ c) := by
  apply Axioms.or_elim h_ab
  · intro h_lt_ab
    exact Axioms.or_intro_left (lt_le_trans h_lt_ab h_bc)
  · intro h_eq_ab
    apply Axioms.or_elim h_bc
    · intro h_lt_bc
      exact Axioms.or_intro_left (le_lt_trans (Axioms.or_intro_right h_eq_ab) h_lt_bc)
    · intro h_eq_bc
      exact Axioms.or_intro_right (eq_trans (eq_symm h_eq_ab) h_eq_bc)

-- Lema Auxiliar: a ≤ b ∧ c > 0 ⇒ a*c ≤ b*c
theorem mul_le_mono_right {a b c : Term} (h_le : Γ ⊢ (a ≤ b)) (h_c_pos : Γ ⊢ lt zero c) :
    Γ ⊢ ((mul a c) ≤ (mul b c)) := by
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax9  := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_ax12 := ax (by simp [axioms] : ax12_mul_distrib ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  apply Axioms.or_elim h_le
  · intro h_lt_ab
    apply Axioms.or_intro_left
    -- Extract kp: a + succ kp = b
    have h_iff_ab := spec (spec h_ax13 a) b
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at h_iff_ab
    apply ex_elim (iff_mp h_iff_ab h_lt_ab)
    intro kp h_kp
    simp [substFormula, substTerm, substTerms,
          FOL.substTerm_liftTerm
          ] at h_kp
    -- Extract j: zero + succ j = c
    have h_iff_0c := spec (spec h_ax13 zero) c
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at h_iff_0c
    apply ex_elim (iff_mp h_iff_0c h_c_pos)
    intro j h_j
    simp [substFormula, substTerm, substTerms, zero,
          liftTerm, liftTerms, FOL.substTerm_liftTerm
          ] at h_j
    -- zero + succ j = succ j  (teo_2_2)
    have h_0sj : Γ ⊢ (add zero (succ j) =eq succ j) := by
      have hs := spec teo_2_2 (succ j)
      simp [substFormula, substTerm, substTerms, add, zero, succ
            ] at hs
      exact hs
    -- succ j = c
    have h_sj_c : Γ ⊢ (succ j =eq c) := eq_trans h_0sj h_j
    -- (a + succ kp)*c = c*(a + succ kp)  [ax10]
    have h_comm1 : Γ ⊢ (mul (add a (succ kp)) c =eq mul c (add a (succ kp))) := by
      have h := spec (spec h_ax10 (add a (succ kp))) c
      simp [substFormula, substTerm, substTerms, mul, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm] at h
      exact h
    -- c*(a + succ kp) = c*a + c*(succ kp)  [ax12]
    have h_distrib : Γ ⊢ (mul c (add a (succ kp)) =eq add (mul c a) (mul c (succ kp))) := by
      have h := spec (spec (spec h_ax12 c) a) (succ kp)
      simp [substFormula, substTerm, substTerms, mul, add, succ,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h
      exact h
    -- c*a = a*c  [ax10]
    have h_comm_ca : Γ ⊢ (mul c a =eq mul a c) := by
      have h := spec (spec h_ax10 c) a
      simp [substFormula, substTerm, substTerms, mul,
            FOL.substTerm_liftTerm] at h
      exact h
    -- c*(succ kp) = (succ kp)*c  [ax10]
    have h_comm_cskp : Γ ⊢ (mul c (succ kp) =eq mul (succ kp) c) := by
      have h := spec (spec h_ax10 c) (succ kp)
      simp [substFormula, substTerm, substTerms, mul, succ,
            FOL.substTerm_liftTerm] at h
      exact h
    -- (a + succ kp)*c = a*c + (succ kp)*c
    have h_right_distrib : Γ ⊢ (mul (add a (succ kp)) c =eq add (mul a c) (mul (succ kp) c)) :=
      FOL.derive_eq_trans h_comm1
        (FOL.derive_eq_trans h_distrib
          (FOL.derive_eq_trans
            (eq_congr_add_right h_comm_ca)
            (eq_congr_add_left h_comm_cskp)))
    -- b*c = (a + succ kp)*c  [since b = a + succ kp]
    have h_bc_rhs : Γ ⊢ (mul b c =eq mul (add a (succ kp)) c) :=
      eq_congr_mul_right (eq_symm h_kp)
    -- b*c = a*c + (succ kp)*c
    have h_bc_expand : Γ ⊢ (mul b c =eq add (mul a c) (mul (succ kp) c)) :=
      FOL.derive_eq_trans h_bc_rhs h_right_distrib
    -- (succ kp)*c = (succ kp)*(succ j)  [since c = succ j]
    have h_skp_c_sj : Γ ⊢ (mul (succ kp) c =eq mul (succ kp) (succ j)) :=
      eq_symm (eq_congr_mul_left h_sj_c)
    -- (succ kp)*(succ j) = (succ kp)*j + succ kp  [ax9]
    have h_skp_sj : Γ ⊢ (mul (succ kp) (succ j) =eq add (mul (succ kp) j) (succ kp)) := by
      have h := spec (spec h_ax9 (succ kp)) j
      simp [substFormula, substTerm, substTerms, mul, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm] at h
      exact h
    -- (succ kp)*j + succ kp = succ((succ kp)*j + kp)  [ax5]
    have h_add_succ : Γ ⊢ (add (mul (succ kp) j) (succ kp) =eq succ (add (mul (succ kp) j) kp)) := by
      have h := spec (spec h_ax5 (mul (succ kp) j)) kp
      simp [substFormula, substTerm, substTerms, add, succ,
            FOL.substTerm_liftTerm] at h
      exact h
    -- (succ kp)*c = succ((succ kp)*j + kp)
    have h_skp_c_succ : Γ ⊢ (mul (succ kp) c =eq succ (add (mul (succ kp) j) kp)) :=
      FOL.derive_eq_trans h_skp_c_sj (FOL.derive_eq_trans h_skp_sj h_add_succ)
    -- b*c = a*c + succ((succ kp)*j + kp)
    have h_bc_final : Γ ⊢ (mul b c =eq add (mul a c) (succ (add (mul (succ kp) j) kp))) :=
      FOL.derive_eq_trans h_bc_expand (eq_congr_add_left h_skp_c_succ)
    -- lt (mul a c) (mul b c) via ax13, witness = (succ kp)*j + kp
    have h_iff_mac_mbc := spec (spec h_ax13 (mul a c)) (mul b c)
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_liftTerm,
          FOL.substTerm_liftLift] at h_iff_mac_mbc
    apply iff_mpr h_iff_mac_mbc
    exact ex_intro (add (mul (succ kp) j) kp) (by
      simp [substFormula, substTerm, substTerms, add, succ,
            FOL.substTerm_liftTerm
            ]
      exact eq_symm h_bc_final)
  · intro h_eq_ab
    exact Axioms.or_intro_right (eq_congr_mul_right h_eq_ab)

-- Lema Auxiliar: a ≤ b ⇒ a² ≤ b²
theorem sq_le_mono {a b : Term} (h_le : Γ ⊢ (a ≤ b)) : Γ ⊢ ((sq a) ≤ (sq b)) := by
  have h_ax10 := ax (by simp [axioms] : ax10_mul_comm ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  unfold sq
  have h_tric : Γ ⊢ (lt zero a ∨ (zero =eq a) ∨ lt a zero) := by
    have h := spec (spec h_ax19 zero) a
    simp [substFormula, substTerm, substTerms, lt,
          FOL.substTerm_liftTerm] at h
    exact h
  apply Axioms.or_elim h_tric
  · intro h_a_pos
    -- a > 0: mul a a ≤ mul b a ≤ mul b b
    have h_b_pos : Γ ⊢ lt zero b := lt_le_trans h_a_pos h_le
    -- mul a a ≤ mul b a  (mul_le_mono_right with c = a)
    have h1 : Γ ⊢ ((mul a a) ≤ (mul b a)) := mul_le_mono_right h_le h_a_pos
    -- mul b a = mul a b  [ax10]
    have h_ba_ab : Γ ⊢ (mul b a =eq mul a b) := by
      have h := spec (spec h_ax10 b) a
      simp [substFormula, substTerm, substTerms, mul,
            FOL.substTerm_liftTerm] at h
      exact h
    -- mul a b ≤ mul b b  (mul_le_mono_right with c = b)
    have h2 : Γ ⊢ ((mul a b) ≤ (mul b b)) := mul_le_mono_right h_le h_b_pos
    -- mul b a ≤ mul b b
    have h3 : Γ ⊢ ((mul b a) ≤ (mul b b)) := le_trans (Axioms.or_intro_right h_ba_ab) h2
    exact le_trans h1 h3
  · intro h23
    apply Axioms.or_elim h23
    · intro h_a0  -- zero =eq a
      -- mul a a = zero (via mul zero a = zero, since a = 0)
      have h_a_eq_zero : Γ ⊢ (a =eq zero) := eq_symm h_a0
      have h_ma_eq_mza : Γ ⊢ (mul a a =eq mul zero a) :=
        eq_congr_mul_right h_a_eq_zero
      have h_mza_eq_zero : Γ ⊢ (mul zero a =eq zero) := by
        have hs := spec teo_2_4 a
        simp [substFormula, substTerm, substTerms, mul, zero
              ] at hs
        exact hs
      have h_maa_eq_zero : Γ ⊢ (mul a a =eq zero) :=
        FOL.derive_eq_trans h_ma_eq_mza h_mza_eq_zero
      -- zero ≤ mul b b
      exact le_trans (Axioms.or_intro_right h_maa_eq_zero) (zero_le (mul b b))
    · intro h_lt_a0  -- a < zero: impossible
      apply false_elim
      have h_ax2  := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
      have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
      have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
      have hh := spec (spec h_ax13 a) zero
      simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms,
            FOL.substTerm_liftTerm] at hh
      apply ex_elim (iff_mp hh h_lt_a0)
      intro k h_k
      simp [substFormula, substTerm, substTerms,
            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_k
      have h_step : Γ ⊢ (add a (succ k) =eq succ (add a k)) := by
        have hs := spec (spec h_ax5 a) k
        simp [substFormula, substTerm, substTerms, add, succ,
              FOL.substTerm_liftTerm] at hs
        exact hs
      have h_neq0 : Γ ⊢ neg (succ (add a k) =eq zero) := by
        have hn := spec h_ax2 (add a k)
        simp [succ
              ] at hn
        exact hn
      exact mp h_neq0 (eq_trans h_step h_k)

-- Teo 4.6: k² ≤ n ∧ n < (k+1)² ⇒ k = √n  (Unicidad)
theorem sqrt_unique_of_bounds {k n : Term} :
    Γ ⊢ ((sq k ≤ n) ∧ lt n (sq (succ k))) ⇒ (k =eq (sqrt n)) := by
  have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  apply Axioms.imp_intro; intro h_bounds
  have h_sq_k_le_n   : Γ ⊢ (sq k ≤ n)            := Axioms.and_elim_left h_bounds
  have h_n_lt_sq_sk  : Γ ⊢ lt n (sq (succ k))     := Axioms.and_elim_right h_bounds
  -- Trichotomy: k < √n ∨ k = √n ∨ √n < k
  have h_tric : Γ ⊢ (lt k (sqrt n) ∨ (k =eq sqrt n) ∨ lt (sqrt n) k) := by
    have h := spec (spec h_ax19 k) (sqrt n)
    simp [substFormula, substTerm, substTerms, lt, sqrt,
          FOL.substTerm_liftTerm] at h
    exact h
  apply Axioms.or_elim h_tric
  · intro h_k_lt_sqrtn
    apply false_elim
    -- succ k ≤ sqrt n
    have h_sk_le       : Γ ⊢ ((succ k) ≤ (sqrt n))     := succ_le_of_lt h_k_lt_sqrtn
    -- sq (succ k) ≤ sq (sqrt n)
    have h_sq_sk_le    : Γ ⊢ ((sq (succ k)) ≤ (sq (sqrt n))) := sq_le_mono h_sk_le
    -- sq (sqrt n) ≤ n
    have h_sq_sqrt_le  : Γ ⊢ ((sq (sqrt n)) ≤ n)        := sqrt_sq_le n
    -- sq (succ k) ≤ n
    have h_sq_sk_le_n  : Γ ⊢ ((sq (succ k)) ≤ n)        := le_trans h_sq_sk_le h_sq_sqrt_le
    -- n < sq (succ k) ≤ n  →  n < n
    have h_lt_nn : Γ ⊢ lt n n := lt_le_trans h_n_lt_sq_sk h_sq_sk_le_n
    have h_irr := spec h_ax18 n
    simp [lt
          ] at h_irr
    exact mp h_irr h_lt_nn
  · intro h23
    apply Axioms.or_elim h23
    · intro h_eq; exact h_eq
    · intro h_sqrtn_lt_k
      apply false_elim
      -- succ (sqrt n) ≤ k
      have h_ssqrtn_le    : Γ ⊢ ((succ (sqrt n)) ≤ k)          := succ_le_of_lt h_sqrtn_lt_k
      -- sq (succ (sqrt n)) ≤ sq k
      have h_sq_ssqrtn_le : Γ ⊢ ((sq (succ (sqrt n))) ≤ (sq k)) := sq_le_mono h_ssqrtn_le
      -- sq (succ (sqrt n)) ≤ n
      have h_sq_ssqrtn_le_n : Γ ⊢ ((sq (succ (sqrt n))) ≤ n)   := le_trans h_sq_ssqrtn_le h_sq_k_le_n
      -- n < sq (succ (sqrt n))
      have h_n_lt_ssq : Γ ⊢ lt n (sq (succ (sqrt n)))           := lt_succ_sqrt_sq n
      -- n < n
      have h_lt_nn : Γ ⊢ lt n n := lt_le_trans h_n_lt_ssq h_sq_ssqrtn_le_n
      have h_irr := spec h_ax18 n
      simp [lt
            ] at h_irr
      exact mp h_irr h_lt_nn

-- Teo 4.4: √0 = 0
theorem sqrt_zero : Γ ⊢ ((sqrt zero) =eq zero) := by
  have h_le : Γ ⊢ (sq (sqrt zero) ≤ zero) := sqrt_sq_le zero
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax2  := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  have lt_zero_impossible : ∀ x : Term, axioms ⊢ lt x zero → axioms ⊢ ⊥ := fun x h_ltx0 => by
    have hh := spec (spec h_ax13 x) zero
    simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at hh
    apply ex_elim (iff_mp hh h_ltx0)
    intro k h_k
    simp [substFormula, substTerm, substTerms,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_k
    have h_step : axioms ⊢ (add x (succ k) =eq succ (add x k)) := by
      have hs := spec (spec h_ax5 x) k
      simp [substFormula, substTerm, substTerms, add, succ,
            FOL.substTerm_liftTerm] at hs
      exact hs
    have h_neq0 : axioms ⊢ neg (succ (add x k) =eq zero) := by
      have hn := spec h_ax2 (add x k)
      simp [succ
            ] at hn
      exact hn
    exact mp h_neq0 (eq_trans h_step h_k)
  apply Axioms.or_elim h_le
  · intro h_lt
    exact false_elim (lt_zero_impossible (sq (sqrt zero)) h_lt)
  · intro h_eq
    exact mp (sq_eq_zero_imp_zero (sqrt zero)) h_eq

-- Teo 4.5: √1 = 1
theorem sqrt_one : Γ ⊢ ((sqrt one) =eq one) := by
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax2  := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  have h_ax3  := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax18 := ax (by simp [axioms] : ax18_lt_irrefl ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_lt15 : Γ ⊢ lt one (sq (succ (sqrt one))) := lt_succ_sqrt_sq one
  have h_tric : Γ ⊢ (lt (sqrt one) one ∨ ((sqrt one) =eq one) ∨ lt one (sqrt one)) := by
    have h := spec (spec h_ax19 (sqrt one)) one
    simp [substFormula, substTerm, substTerms, lt, sqrt, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at h
    exact h
  have lt_zero_impossible : ∀ x : Term, axioms ⊢ lt x zero → axioms ⊢ ⊥ := fun x h_ltx0 => by
    have hh := spec (spec h_ax13 x) zero
    simp [substFormula, substTerm, substTerms, lt, add, succ, zero, iff, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at hh
    apply ex_elim (iff_mp hh h_ltx0)
    intro k h_k
    simp [substFormula, substTerm, substTerms,
          FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at h_k
    have h_step : axioms ⊢ (add x (succ k) =eq succ (add x k)) := by
      have hs := spec (spec h_ax5 x) k
      simp [substFormula, substTerm, substTerms, add, succ,
            FOL.substTerm_liftTerm] at hs
      exact hs
    have h_neq0 : axioms ⊢ neg (succ (add x k) =eq zero) := by
      have hn := spec h_ax2 (add x k)
      simp [succ
            ] at hn
      exact hn
    exact mp h_neq0 (eq_trans h_step h_k)
  apply Axioms.or_elim h_tric
  · -- Caso √1 < 1
    intro h_sqrt_lt_1
    have hh := spec (spec h_ax13 (sqrt one)) one
    simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
          FOL.substTerm_lift_comm, FOL.substTerm_liftTerm] at hh
    apply ex_elim (iff_mp hh h_sqrt_lt_1)
    intro k h_k
    simp [substFormula, substTerm, substTerms,
          FOL.substTerm_liftTerm] at h_k
    have h_ax5_inst : axioms ⊢ (add (sqrt one) (succ k) =eq succ (add (sqrt one) k)) := by
      have hs := spec (spec h_ax5 (sqrt one)) k
      simp [substFormula, substTerm, substTerms, add, succ,
            FOL.substTerm_liftTerm] at hs
      exact hs
    have h_succ_eq : axioms ⊢ (succ (add (sqrt one) k) =eq succ zero) :=
      eq_trans h_ax5_inst h_k
    have h_ax3_inst : axioms ⊢
        ((succ (add (sqrt one) k) =eq succ zero) ⇒ (add (sqrt one) k =eq zero)) := by
      have hw := spec (spec h_ax3 (add (sqrt one) k)) zero
      simp [substFormula, substTerm, substTerms, succ,
            FOL.substTerm_liftTerm] at hw
      exact hw
    have h_sum0 : axioms ⊢ (add (sqrt one) k =eq zero) := mp h_ax3_inst h_succ_eq
    have h_teo29_inst : axioms ⊢
        (add (sqrt one) k =eq zero) ⇒ (land ((sqrt one) =eq zero) (k =eq zero)) := by
      have hs := spec (spec teo_2_9 (sqrt one)) k
      simp [substFormula, substTerm, substTerms, add, zero, land,
            FOL.substTerm_liftTerm] at hs
      exact hs
    have h_sqrt1_eq0 : axioms ⊢ ((sqrt one) =eq zero) :=
      Axioms.and_elim_left (mp h_teo29_inst h_sum0)
    have h_succ_sqrt1_eq1 : axioms ⊢ (succ (sqrt one) =eq one) :=
      eq_congr_succ h_sqrt1_eq0
    -- sq(σ(√1)) = one
    have h_sq_succ_eq1 : axioms ⊢ (sq (succ (sqrt one)) =eq one) := by
      unfold sq
      have step1 : axioms ⊢ (mul (succ (sqrt one)) (succ (sqrt one)) =eq mul one (succ (sqrt one))) :=
        eq_congr_mul_right h_succ_sqrt1_eq1
      have step2 : axioms ⊢ (mul one (succ (sqrt one)) =eq mul one one) :=
        eq_congr_mul_left h_succ_sqrt1_eq1
      have step3 : axioms ⊢ (mul one one =eq one) := teo_1_8
      exact FOL.derive_eq_trans (FOL.derive_eq_trans step1 step2) step3
    -- 1 < sq(σ(√1)) → ∃j, 1 + σj = sq(σ(√1))
    have h_lt15_ex : axioms ⊢ ex (add one (succ (.var 0)) =eq sq (succ (sqrt one))) := by
      have h := spec (spec h_ax13 one) (sq (succ (sqrt one)))
      simp [substFormula, substTerm, substTerms, lt, add, succ, one, iff, liftTerm, liftTerms,
            FOL.substTerm_liftTerm, FOL.substTerm_lift_comm] at h
      exact iff_mp h h_lt15
    apply ex_elim h_lt15_ex
    intro j h_j
    -- h_j is definitionally: add one (succ j) =eq sq (succ (sqrt one))
    have h_j' : axioms ⊢ (add one (succ j) =eq sq (succ (sqrt one))) := h_j
    have h_j_eq1 : axioms ⊢ (add one (succ j) =eq one) :=
      FOL.derive_eq_trans h_j' h_sq_succ_eq1
    have h_ax5_j : axioms ⊢ (add one (succ j) =eq succ (add one j)) := by
      have hs := spec (spec h_ax5 one) j
      simp [substFormula, substTerm, substTerms, add, succ,
            FOL.substTerm_liftTerm] at hs
      exact hs
    have h_succ_eq0 : axioms ⊢ (succ (add one j) =eq succ zero) :=
      eq_trans h_ax5_j h_j_eq1
    have h_ax3_j : axioms ⊢
        ((succ (add one j) =eq succ zero) ⇒ (add one j =eq zero)) := by
      have hw := spec (spec h_ax3 (add one j)) zero
      simp [substFormula, substTerm, substTerms, succ,
            FOL.substTerm_liftTerm] at hw
      exact hw
    have h_one_j_0 : axioms ⊢ (add one j =eq zero) := mp h_ax3_j h_succ_eq0
    have h_teo29_j : axioms ⊢
        (add one j =eq zero) ⇒ (land (one =eq zero) (j =eq zero)) := by
      have hs := spec (spec teo_2_9 one) j
      simp [substFormula, substTerm, substTerms, add, zero, land,
            FOL.substTerm_liftTerm] at hs
      exact hs
    have h_one_eq0 : axioms ⊢ (one =eq zero) :=
      Axioms.and_elim_left (mp h_teo29_j h_one_j_0)
    have h_one_neq0 : axioms ⊢ neg (succ zero =eq zero) := by
      have hn := spec h_ax2 zero
      simp [succ
            ] at hn
      exact hn
    exact false_elim (mp h_one_neq0 h_one_eq0)
  · intro h23
    apply Axioms.or_elim h23
    · intro h_eq; exact h_eq
    · intro h_large  -- lt one (sqrt one)
      apply false_elim
      -- succ one ≤ sqrt one  (= two ≤ sqrt one)
      have h_two_le_sqrt1 : Γ ⊢ ((succ one) ≤ (sqrt one)) := succ_le_of_lt h_large
      -- sq (succ one) ≤ sq (sqrt one)
      have h_sq_two_le : Γ ⊢ ((sq (succ one)) ≤ (sq (sqrt one))) := sq_le_mono h_two_le_sqrt1
      -- sq (sqrt one) ≤ one
      have h_sq_sqrt1_le_1 : Γ ⊢ ((sq (sqrt one)) ≤ one) := sqrt_sq_le one
      -- sq (succ one) ≤ one
      have h_sq_two_le_1 : Γ ⊢ ((sq (succ one)) ≤ one) :=
        le_trans h_sq_two_le h_sq_sqrt1_le_1
      -- sq (succ one) = mul two two = four  [teo_1_10, since succ one = two definitionally]
      have h_sq_two_is_four : Γ ⊢ ((sq (succ one)) =eq four) := teo_1_10
      -- one < four: add one (succ two) = succ(add one two) = succ three = four
      have h_1lt4 : Γ ⊢ lt one four := by
        have h_ax5_one_two : Γ ⊢ (add one (succ two) =eq succ (add one two)) := by
          have hs := spec (spec h_ax5 one) two
          simp [substFormula, substTerm, substTerms, add, succ,
                FOL.substTerm_liftTerm] at hs
          exact hs
        have h_iff := spec (spec h_ax13 one) four
        simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
              FOL.substTerm_liftTerm,
              FOL.substTerm_liftLift] at h_iff
        apply iff_mpr h_iff
        exact ex_intro two (by
          simp [substFormula, substTerm, substTerms,
                FOL.substTerm_liftTerm]
          exact FOL.derive_eq_trans h_ax5_one_two (eq_congr_succ teo_1_5))
      -- Case split on sq(succ one) ≤ one
      apply Axioms.or_elim h_sq_two_le_1
      · intro h_sq2_lt_1  -- lt (sq (succ one)) one
        -- Derive lt four one via Derives.subst with sq(succ one) = four
        have h_4lt1 : Γ ⊢ lt four one := by
          let f := Formula.atom lt_sym [.var 0, liftTerm 0 one]
          have hS : ∀ s, substFormula 0 s f = lt s one := fun s => by
            simp [f, substFormula, substTerm, substTerms, lt,
                  FOL.substTerm_liftTerm]
          exact (hS four) ▸ Derives.subst Γ (sq (succ one)) four f h_sq_two_is_four
                                             ((hS (sq (succ one))).symm ▸ h_sq2_lt_1)
        -- lt one four and lt four one → lt one one → contradiction
        have h_lt_one_one : Γ ⊢ lt one one :=
          lt_le_trans h_1lt4 (Axioms.or_intro_left h_4lt1)
        have h_irr := spec h_ax18 one
        simp [lt
              ] at h_irr
        exact mp h_irr h_lt_one_one
      · intro h_sq2_eq_1  -- sq (succ one) = one
        -- sq(succ one) = four AND sq(succ one) = one → four = one → three = zero → ⊥
        have h_4eq1 : Γ ⊢ (four =eq one) := eq_trans h_sq_two_is_four h_sq2_eq_1
        -- ax3 with three and zero: (succ three = succ zero) ⇒ (three = zero)
        -- i.e., (four = one) ⇒ (three = zero)
        have h_ax3_inst : Γ ⊢ ((four =eq one) ⇒ (three =eq zero)) := by
          have hw := spec (spec h_ax3 three) zero
          simp [substFormula, substTerm, substTerms, succ,
                FOL.substTerm_liftTerm] at hw
          exact hw
        have h_three_eq_zero : Γ ⊢ (three =eq zero) := mp h_ax3_inst h_4eq1
        -- three = succ two ≠ zero  [ax2 with two]
        have h_three_neq0 : Γ ⊢ neg (three =eq zero) := by
          have hn := spec h_ax2 two
          simp [succ
                ] at hn
          exact hn
        exact mp h_three_neq0 h_three_eq_zero

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
  zero_le
  mul_le_mono_right
  sq_le_mono
)
