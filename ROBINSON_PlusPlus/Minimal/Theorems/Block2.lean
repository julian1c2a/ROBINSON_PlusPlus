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
  -- sq n = mul n n. Si n*n=0, por teo_2_10: n=0 ∨ n=0, luego n=0.
  apply Axioms.imp_intro; intro h_sq0
  have h_teo210_inst : Γ ⊢ ((mul n n =eq zero) ⇒ lor (n =eq zero) (n =eq zero)) := by
    have h := spec (spec teo_2_10 n) n
    simp [substFormula, substTerm, substTerms, mul, lor, land, liftTerm, liftTerms,
          FOL.substTerm_liftTerm] at h
    exact h
  have h_or := mp h_teo210_inst h_sq0
  apply Axioms.or_elim h_or
  · intro h; exact h
  · intro h; exact h

-- Teorema (antes Ax 22): a < b ⇒ σ(a) ≤ b
-- Prueba siguiendo THOUGHTS.md §"¿Es necesario el axioma 22?"
theorem succ_le_of_lt {a b : Term} (h_lt : Γ ⊢ lt a b) : Γ ⊢ ((succ a) ≤ b) := by
  -- Paso 1: Tricotomía para σ(a) y b (ax19)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_tric : Γ ⊢ (lt (succ a) b ∨ (succ a =eq b) ∨ lt b (succ a)) := by
    have h := spec (spec h_ax19 (succ a)) b
    -- h : Γ ⊢ substFormula 0 b (substFormula 1 (liftTerm 0 (succ a)) body19)
    -- que computa a  lt(σa,b) ∨ (σa =eq b) ∨ lt(b,σa)
    -- via FOL.substTerm_liftTerm (substTerm c s (liftTerm c t) = t)
    -- y reducción de los índices de de Bruijn numéricos
    simp [substFormula, substTerm, substTerms,
          liftTerm, liftTerms, lt, succ, FOL.substTerm_liftTerm] at h
    exact h
  -- Paso 2: or_elim en modo táctico (el goal provee el tipo implícito B para or_intro_left/right)
  apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_tric
  · intro h1; exact ROBINSON_PlusPlus.Minimal.Axioms.or_intro_left h1   -- caso lt (succ a) b
  · intro h23
    apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h23
    · intro h2; exact ROBINSON_PlusPlus.Minimal.Axioms.or_intro_right h2  -- caso succ a = b
    · intro h_blt_sa
      -- Paso 3: caso b < σ(a) — contradicción con h_lt : a < b
      -- Helper lt_to_ex: Γ ⊢ lt x y → ∃ k : Term, Γ ⊢ (add x (succ k) =eq y)
      have lt_to_ex : ∀ (x y : Term), Γ ⊢ lt x y → ∃ k : Term, Γ ⊢ (add x (succ k) =eq y) := by
        intro x y h_xy
        have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
        have h_ax13_xy := by
          have h := spec (spec h_ax13 x) y
          simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
                liftTerm, liftTerms, FOL.substTerm_liftTerm,
                FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h
          exact h
        have h_ex := iff_mp h_ax13_xy h_xy
        exact ⟨_, by
          apply ex_elim h_ex; intro k h_k
          simp [substFormula, substTerm, substTerms, add, succ,
                liftTerm, liftTerms, FOL.substTerm_liftTerm,
                FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_k
          exact h_k⟩
      obtain ⟨kp, h_kp⟩ := lt_to_ex a b h_lt
      obtain ⟨k, h_k⟩ := lt_to_ex b (succ a) h_blt_sa
      -- h_kp : a + σ(kp) = b
      -- h_k  : b + σ(k) = σ(a)
      -- Contradicción: cadena aritmética → σ(kp) = 0 → ↯ ax2
      exact false_elim (by
        have h_ax2  := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
        have h_ax3  := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
        have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
        have h_ax7  := ax (by simp [axioms] : ax7_add_assoc ∈ axioms)
        have h_ax27 := ax (by simp [axioms] : ax27_add_left_cancel ∈ axioms)
        -- Sustituir b: (a + σ(kp)) + σ(k) = σ(a)
        have h_sub : axioms ⊢ (add (add a (succ kp)) (succ k) =eq succ a) :=
          eq_trans (eq_congr_add_right (eq_symm h_kp)) h_k
        -- ax7: (a + σ(kp)) + σ(k) = a + (σ(kp) + σ(k))
        have h_ax7_inst : axioms ⊢ (add (add a (succ kp)) (succ k) =eq add a (add (succ kp) (succ k))) := by
          have ha := spec (spec (spec h_ax7 a) (succ kp)) (succ k)
          simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
                FOL.substTerm_liftTerm, FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at ha
          exact ha
        -- a + (σ(kp) + σ(k)) = σ(a)  [eq_trans h_ax7_inst h_sub]
        have h_mid : axioms ⊢ (add a (add (succ kp) (succ k)) =eq succ a) :=
          eq_trans h_ax7_inst h_sub
        -- ax5: σ(kp) + σ(k) = σ(σ(kp) + k)
        have h_ax5_inst : axioms ⊢ (add (succ kp) (succ k) =eq succ (add (succ kp) k)) := by
          have hs := spec (spec h_ax5 (succ kp)) k
          simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
                FOL.substTerm_liftTerm] at hs
          exact hs
        -- a + σ(σ(kp)+k) = σ(a)
        have h_mid2 : axioms ⊢ (add a (succ (add (succ kp) k)) =eq succ a) :=
          eq_trans (eq_congr_add_left h_ax5_inst) h_mid
        -- teo_2_8: σ(a) = a + 1
        have h_sa_eq : axioms ⊢ (succ a =eq add a one) := by
          have hs := spec teo_2_8 a
          simp [substFormula, substTerm, substTerms, succ, liftTerm, liftTerms,
                FOL.substTerm_liftTerm] at hs
          exact hs
        -- a + σ(σ(kp)+k) = a + 1  [eq_trans (eq_symm h_mid2) h_sa_eq]
        have h_mid3 : axioms ⊢ (add a (succ (add (succ kp) k)) =eq add a one) :=
          eq_trans (eq_symm h_mid2) h_sa_eq
        -- ax27: cancela a → σ(σ(kp)+k) = 1
        have h_ax27_inst : axioms ⊢
            ((add a (succ (add (succ kp) k)) =eq add a one) ⇒ (succ (add (succ kp) k) =eq one)) := by
          have hw := spec (spec (spec h_ax27 a) (succ (add (succ kp) k))) one
          simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
                FOL.substTerm_liftTerm, FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at hw
          exact hw
        have h_eq_one : axioms ⊢ (succ (add (succ kp) k) =eq one) :=
          mp h_ax27_inst h_mid3
        -- σ(σ(kp)+k) = σ(0)
        have h_eq_succ0 : axioms ⊢ (succ (add (succ kp) k) =eq succ zero) := by
          have : one = succ zero := rfl; rw [← this]; exact h_eq_one
        -- ax3: σ(kp)+k = 0
        have h_ax3_inst : axioms ⊢
            ((succ (add (succ kp) k) =eq succ zero) ⇒ (add (succ kp) k =eq zero)) := by
          have hw := spec (spec h_ax3 (add (succ kp) k)) zero
          simp [substFormula, substTerm, substTerms, succ, liftTerm, liftTerms,
                FOL.substTerm_liftTerm, FOL.substTerm_lift_comm] at hw
          exact hw
        have h_sum0 : axioms ⊢ (add (succ kp) k =eq zero) := mp h_ax3_inst h_eq_succ0
        -- teo_2_9: σ(kp) = 0
        have h_teo29_inst : axioms ⊢
            (add (succ kp) k =eq zero) ⇒ (land (succ kp =eq zero) (k =eq zero)) := by
          have hs := spec (spec teo_2_9 (succ kp)) k
          simp [substFormula, substTerm, substTerms, add, zero, land, liftTerm, liftTerms,
                FOL.substTerm_liftTerm] at hs
          exact hs
        have h_skp0 : axioms ⊢ (succ kp =eq zero) :=
          Axioms.and_elim_left (mp h_teo29_inst h_sum0)
        -- ax2: σ(kp) ≠ 0
        have h_ax2_inst : axioms ⊢ neg (succ kp =eq zero) := by
          have hn := spec h_ax2 kp
          simp [substFormula, substTerm, substTerms, succ, liftTerm, liftTerms,
                FOL.substTerm_liftTerm] at hn
          exact hn
        exact mp h_ax2_inst h_skp0)

-- Lema Auxiliar: a ≤ b ∧ c > 0 ⇒ a*c ≤ b*c
private theorem mul_le_mono_right {a b c : Term} (h_le : Γ ⊢ (a ≤ b)) (h_c_pos : Γ ⊢ lt zero c) : Γ ⊢ ((mul a c) ≤ (mul b c)) := by
  sorry

-- Lema Auxiliar: a ≤ b ⇒ a² ≤ b²
private theorem sq_le_mono {a b : Term} (h_le : Γ ⊢ (a ≤ b)) : Γ ⊢ ((sq a) ≤ (sq b)) := by
  sorry -- Depends on mul_le_mono_right.

-- Lemas auxiliares de transitividad
theorem lt_le_trans {a b c : Term} (h_lt : Γ ⊢ lt a b) (h_le : Γ ⊢ (b ≤ c)) : Γ ⊢ lt a c := by
  have lt_to_ex : ∀ (x y : Term), Γ ⊢ lt x y → ∃ k : Term, Γ ⊢ (add x (succ k) =eq y) := by
    intro x y h_xy
    have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
    have h_ax13_xy := by
      have h := spec (spec h_ax13 x) y
      simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
            liftTerm, liftTerms, FOL.substTerm_liftTerm,
            FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h
      exact h
    have h_ex := iff_mp h_ax13_xy h_xy
    exact ⟨_, by
      apply ex_elim h_ex; intro k h_k
      simp [substFormula, substTerm, substTerms, add, succ,
            liftTerm, liftTerms, FOL.substTerm_liftTerm,
            FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_k
      exact h_k⟩
  have ex_to_lt_ac : (∃ k : Term, Γ ⊢ (add a (succ k) =eq c)) → Γ ⊢ lt a c := by
    intro ⟨k, h_k⟩
    have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
    have h_iff := by
      have h := spec (spec h_ax13 a) c
      simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
            liftTerm, liftTerms, FOL.substTerm_liftTerm,
            FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h
      exact h
    apply iff_mpr h_iff
    exact ex_intro k (by
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm, FOL.substTerm_lift_comm, FOL.substTerm_liftLift]
      exact h_k)
  apply Axioms.or_elim h_le
  · intro h_lt_bc
    obtain ⟨j, h_j⟩ := lt_to_ex a b h_lt
    obtain ⟨k, h_k⟩ := lt_to_ex b c h_lt_bc
    have h_sub : Γ ⊢ (add (add a (succ j)) (succ k) =eq c) :=
      eq_trans (eq_congr_add_right (eq_symm h_j)) h_k
    have h_ax7 := ax (by simp [axioms] : ax7_add_assoc ∈ axioms)
    have h_assoc : Γ ⊢ (add (add a (succ j)) (succ k) =eq add a (add (succ j) (succ k))) := by
      have ha := spec (spec (spec h_ax7 a) (succ j)) (succ k)
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm, FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at ha
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
    obtain ⟨j, h_j⟩ := lt_to_ex a b h_lt
    exact ex_to_lt_ac ⟨j, eq_trans h_j (eq_symm h_eq_bc)⟩

theorem le_lt_trans {a b c : Term} (h_le : Γ ⊢ (a ≤ b)) (h_lt : Γ ⊢ lt b c) : Γ ⊢ lt a c := by
  have lt_to_ex : ∀ (x y : Term), Γ ⊢ lt x y → ∃ k : Term, Γ ⊢ (add x (succ k) =eq y) := by
    intro x y h_xy
    have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
    have h_ax13_xy := by
      have h := spec (spec h_ax13 x) y
      simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
            liftTerm, liftTerms, FOL.substTerm_liftTerm,
            FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h
      exact h
    have h_ex := iff_mp h_ax13_xy h_xy
    exact ⟨_, by
      apply ex_elim h_ex; intro k h_k
      simp [substFormula, substTerm, substTerms, add, succ,
            liftTerm, liftTerms, FOL.substTerm_liftTerm,
            FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h_k
      exact h_k⟩
  have ex_to_lt_ac : (∃ k : Term, Γ ⊢ (add a (succ k) =eq c)) → Γ ⊢ lt a c := by
    intro ⟨k, h_k⟩
    have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
    have h_iff := by
      have h := spec (spec h_ax13 a) c
      simp [substFormula, substTerm, substTerms, lt, add, succ, iff,
            liftTerm, liftTerms, FOL.substTerm_liftTerm,
            FOL.substTerm_lift_comm, FOL.substTerm_liftLift] at h
      exact h
    apply iff_mpr h_iff
    exact ex_intro k (by
      simp [substFormula, substTerm, substTerms, add, succ, liftTerm, liftTerms,
            FOL.substTerm_liftTerm, FOL.substTerm_lift_comm, FOL.substTerm_liftLift]
      exact h_k)
  apply Axioms.or_elim h_le
  · intro h_lt_ab
    exact lt_le_trans h_lt_ab (Axioms.or_intro_left h_lt)
  · intro h_eq_ab
    obtain ⟨k, h_k⟩ := lt_to_ex b c h_lt
    exact ex_to_lt_ac ⟨k, eq_trans (eq_congr_add_right h_eq_ab) h_k⟩

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

-- Teo 4.6: k² ≤ n ∧ n < (k+1)² ⇒ k = √n (Unicidad)
theorem sqrt_unique_of_bounds {k n : Term} : Γ ⊢ ((sq k ≤ n) ∧ lt n (sq (succ k))) ⇒ (k =eq (sqrt n)) := by
  sorry

-- Teo 4.4: √0 = 0
theorem sqrt_zero : Γ ⊢ ((sqrt zero) =eq zero) := by
  sorry

-- Teo 4.5: √1 = 1
theorem sqrt_one : Γ ⊢ ((sqrt one) =eq one) := by
  sorry

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
