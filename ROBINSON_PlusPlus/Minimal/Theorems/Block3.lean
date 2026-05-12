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
import FOL.Deduction

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
-- Prueba: ax21(zero) da (mod2 0=0) ∨ (mod2 0=1). Si mod2 0=1, entonces
-- por ax17(zero): div2(0)*2+mod2(0)=0, i.e., div2(0)*2+1=0 → succ(...)=0 → contradicción con ax2.
theorem mod2_zero : Γ ⊢ (mod2 zero =eq zero) := by
  have h_ax21 := ax (by simp [axioms] : ax21_mod2_range ∈ axioms)
  have h_ax17 := ax (by simp [axioms] : ax17_div_mod_eq ∈ axioms)
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax4  := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax2  := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim (spec h_ax21 zero)
  · intro h; exact h
  · intro h_mod2_1
    -- ax17(zero): add(mul(div2 zero) two)(mod2 zero) =eq zero
    let h17 := spec h_ax17 zero
    -- mod2(0)=1, so add(mul(div2 0) 2)(1) =eq zero
    let h_with_1 := eq_congr_add_left (u := mul (div2 zero) two) h_mod2_1
    -- chain: add(mul(div2 0) two)(mod2 0) =eq add(mul(div2 0) two) one
    -- with h17: add(mul(div2 0) two) one =eq zero
    let h_add1_zero := eq_trans h_with_1 h17
    -- ax5(mul(div2 zero) two, zero): add(mul(div2 0) two) one =eq succ(add(mul(div2 0) two) zero)
    let h_ax5_inst := spec (spec h_ax5 (mul (div2 zero) two)) zero
    -- succ(...) =eq zero
    let h_succ_zero := eq_trans h_ax5_inst h_add1_zero
    -- ax4(mul(div2 0) two): add(mul(div2 0) two) zero =eq mul(div2 0) two
    let h4_inst := spec h_ax4 (mul (div2 zero) two)
    -- succ(mul(div2 0) two) =eq succ(add(mul(div2 0) two) zero)
    let h_succ_eq := eq_symm (eq_congr_succ h4_inst)
    -- succ(mul(div2 0) two) =eq zero
    let h_sn_zero := FOL.derive_eq_trans h_succ_eq h_succ_zero
    -- ax2(mul(div2 0) two): neg(succ(mul(div2 0) two) =eq zero)
    let h_neq := spec h_ax2 (mul (div2 zero) two)
    exact false_elim (mp h_neq h_sn_zero)

-- Teo 5.3: mod2(1) = 1
-- Prueba: ax16(zero): (mod2 0=0) ⇔ (mod2 1=1). iff_mp + mod2_zero.
theorem mod2_one : Γ ⊢ (mod2 one =eq one) :=
  iff_mp (spec (ax (by simp [axioms] : ax16_mod2_succ ∈ axioms)) zero) mod2_zero

-- Teo 5.5: mod2(2) = 0
-- Prueba: ax21(two) da (mod2 2=0) ∨ (mod2 2=1). Si mod2 2=1, entonces
-- ax16(one): (mod2 1=0) ⇔ (mod2 2=1), so iff_mpr → mod2(1)=0, contradice mod2_one + teo_1_11.
theorem mod2_two : Γ ⊢ (mod2 two =eq zero) := by
  have h_ax16 := ax (by simp [axioms] : ax16_mod2_succ ∈ axioms)
  have h_ax21 := ax (by simp [axioms] : ax21_mod2_range ∈ axioms)
  apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim (spec h_ax21 two)
  · intro h; exact h
  · intro h_two_one
    -- ax16(one): (mod2 1=0) ⇔ (mod2 2=1)
    let h_ax16_one := spec h_ax16 one
    -- iff_mpr: mod2 2=1 → mod2 1=0
    let h_one_zero := iff_mpr h_ax16_one h_two_one
    -- eq_trans h_one_zero mod2_one: mod2 1=0 and mod2 1=1 → 0=1
    -- (eq_trans: t1=mod2 1, t2=zero, t3=one → gives zero=one... wait)
    -- eq_trans h1 h2: from h1:(t1=t2) and h2:(t1=t3) gives t2=t3
    -- h_one_zero: mod2 one =eq zero (t1=mod2 one, t2=zero)
    -- mod2_one:   mod2 one =eq one  (t1=mod2 one, t3=one)
    -- eq_trans h_one_zero mod2_one: zero =eq one
    let h_0_1 := eq_trans h_one_zero mod2_one
    exact false_elim (mp teo_1_11 h_0_1)

-- Teo 5.7: mod2(3) = 1
-- Prueba: ax16(two): (mod2 2=0) ⇔ (mod2 3=1). iff_mp + mod2_two.
theorem mod2_three : Γ ⊢ (mod2 three =eq one) :=
  iff_mp (spec (ax (by simp [axioms] : ax16_mod2_succ ∈ axioms)) two) mod2_two

-- Teo 5.9: mod2(4) = 0
-- Prueba: ax21(four) da (mod2 4=0) ∨ (mod2 4=1). Si mod2 4=1,
-- ax16(three): (mod2 3=0) ⇔ (mod2 4=1), iff_mpr → mod2 3=0, contradice mod2_three + teo_1_11.
theorem mod2_four : Γ ⊢ (mod2 four =eq zero) := by
  have h_ax16 := ax (by simp [axioms] : ax16_mod2_succ ∈ axioms)
  have h_ax21 := ax (by simp [axioms] : ax21_mod2_range ∈ axioms)
  apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim (spec h_ax21 four)
  · intro h; exact h
  · intro h_four_one
    let h_ax16_three := spec h_ax16 three
    let h_three_zero := iff_mpr h_ax16_three h_four_one
    let h_0_1 := eq_trans h_three_zero mod2_three
    exact false_elim (mp teo_1_11 h_0_1)


-- ─────────────────────────────────────────────────────────────────
-- § Helper lemmas for div2_*
-- ─────────────────────────────────────────────────────────────────

-- Helper: add(succ a) b = 0 → False
-- Vía ax6(succ a, b): add(succ a) b = add b (succ a)
-- Vía ax5(b, a):      add b (succ a) = succ(add b a)
-- Entonces succ(add b a) = 0 → ax2 ⊥
private theorem add_succ_left_ne_zero (a b : Term)
    (h : Γ ⊢ (add (succ a) b =eq zero)) : Γ ⊢ Formula.bottom := by
  have h_ax2 := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax6 := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
  -- ax6(succ a, b): add(succ a) b = add b (succ a)
  have h6 : Γ ⊢ (add (succ a) b =eq add b (succ a)) := by
    have hh := spec (spec h_ax6 (succ a)) b
    simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
    exact hh
  -- ax5(b, a): add b (succ a) = succ(add b a)
  have h5 : Γ ⊢ (add b (succ a) =eq succ (add b a)) := by
    have hh := spec (spec h_ax5 b) a
    simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
    exact hh
  -- succ(add b a) = 0
  -- h6: add(succ a) b = add b (succ a)
  -- h5: add b (succ a) = succ(add b a)
  -- h: add(succ a) b = 0
  -- chain: succ(add b a) = add b (succ a) [eq_symm h5]
  --        add b (succ a) = add(succ a) b [eq_symm h6]
  --        add(succ a) b = 0 [h]
  have h_seq : Γ ⊢ (succ (add b a) =eq zero) :=
    FOL.derive_eq_trans (eq_symm h5) (FOL.derive_eq_trans (eq_symm h6) h)
  -- neg(succ(add b a) = 0) de ax2
  have h_neq : Γ ⊢ neg (succ (add b a) =eq zero) := by
    have hh := spec h_ax2 (add b a)
    simp [substFormula, substTerm, substTerms, succ, FOL.substTerm_liftTerm] at hh
    exact hh
  exact mp h_neq h_seq

-- Helper: mul (succ t) two ≠ 0
-- Cómputo: mul(succ t) 2 = add(mul(succ t) 0)(succ t) ... = succ(add ... t)
-- Usando ax9, ax8, ax5 y ax2.
-- En lugar de computar paso a paso (que requiere simp genérico), usamos:
-- mul(succ t) 2 = add(mul(succ t) one)(succ t)  [ax9 con arg=one]
-- mul(succ t) one = add(mul(succ t) zero)(succ t) [ax9 con arg=zero]
-- mul(succ t) zero = zero [ax8]
-- → mul(succ t) one = add zero (succ t)
-- ax5(zero, t): add zero (succ t) = succ(add zero t)
-- → mul(succ t) one = succ(add zero t)
-- → mul(succ t) 2 = add(succ(add zero t))(succ t)
-- ax6(succ(add zero t), succ t): = add(succ t)(succ(add zero t))
-- ax5(succ t, add zero t): = succ(add(succ t)(add zero t))
-- → succ(something) ≠ 0 por ax2
private theorem mul_succ_two_ne_zero (t : Term)
    (h : Γ ⊢ (mul (succ t) two =eq zero)) : Γ ⊢ Formula.bottom := by
  have h_ax2 := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax6 := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
  have h_ax8 := ax (by simp [axioms] : ax8_mul_zero ∈ axioms)
  have h_ax9 := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  -- ax9(succ t, one): mul(succ t) 2 = add(mul(succ t) 1)(succ t)
  have h9_2 : Γ ⊢ (mul (succ t) two =eq add (mul (succ t) one) (succ t)) := by
    have hh := spec (spec h_ax9 (succ t)) one
    simp [substFormula, substTerm, substTerms, add, succ, mul, two, one, FOL.substTerm_liftTerm] at hh
    exact hh
  -- ax9(succ t, zero): mul(succ t) 1 = add(mul(succ t) 0)(succ t)
  have h9_1 : Γ ⊢ (mul (succ t) one =eq add (mul (succ t) zero) (succ t)) := by
    have hh := spec (spec h_ax9 (succ t)) zero
    simp [substFormula, substTerm, substTerms, add, succ, mul, one, FOL.substTerm_liftTerm] at hh
    exact hh
  -- ax8(succ t): mul(succ t) zero = zero
  have h8 : Γ ⊢ (mul (succ t) zero =eq zero) := by
    have hh := spec h_ax8 (succ t)
    simp [substFormula, substTerm, substTerms, succ, mul, FOL.substTerm_liftTerm] at hh
    exact hh
  -- mul(succ t) 1 = add zero (succ t)
  -- h9_1: mul(succ t) 1 = add(mul(succ t) 0)(succ t)
  -- eq_congr_add_right h8: add(mul(succ t) 0)(succ t) = add zero (succ t)
  have h_mul1 : Γ ⊢ (mul (succ t) one =eq add zero (succ t)) :=
    FOL.derive_eq_trans h9_1 (eq_congr_add_right (u := succ t) h8)
  -- ax5(zero, t): add zero (succ t) = succ(add zero t)
  have h5_0t : Γ ⊢ (add zero (succ t) =eq succ (add zero t)) := by
    have hh := spec (spec h_ax5 zero) t
    simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
    exact hh
  -- mul(succ t) 1 = succ(add zero t)
  have h_mul1_succ : Γ ⊢ (mul (succ t) one =eq succ (add zero t)) :=
    FOL.derive_eq_trans h_mul1 h5_0t
  -- mul(succ t) 2 = add(succ(add zero t))(succ t)
  have h_mul2 : Γ ⊢ (mul (succ t) two =eq add (succ (add zero t)) (succ t)) :=
    FOL.derive_eq_trans h9_2 (eq_congr_add_right (u := succ t) h_mul1_succ)
  -- add(succ(add zero t))(succ t) = 0 (de h y h_mul2)
  have h_eq : Γ ⊢ (add (succ (add zero t)) (succ t) =eq zero) :=
    FOL.derive_eq_trans (eq_symm h_mul2) h
  -- add(succ X) b = 0 → False (con X = add zero t, b = succ t)
  exact add_succ_left_ne_zero (add zero t) (succ t) h_eq

-- ─────────────────────────────────────────────────────────────────
-- § Teo 5.2: div2(0) = 0
-- ─────────────────────────────────────────────────────────────────

-- Auxiliar: mul(div2 zero) two = zero
-- De ax17(zero): add(mul(div2 zero) two)(mod2 zero) = zero
-- mod2_zero: mod2 zero = zero
-- ax4: add(mul(div2 zero) two) zero = mul(div2 zero) two
-- Entonces: mul(div2 zero) two = zero
private theorem div2_zero_mul : Γ ⊢ (mul (div2 zero) two =eq zero) := by
  have h_ax4  := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax17 := ax (by simp [axioms] : ax17_div_mod_eq ∈ axioms)
  -- ax17(zero): add(mul(div2 0) two)(mod2 0) = zero
  have h17 : Γ ⊢ (add (mul (div2 zero) two) (mod2 zero) =eq zero) := by
    have hh := spec h_ax17 zero
    simp [substFormula, substTerm, substTerms, add, mul, div2, mod2, two, FOL.substTerm_liftTerm] at hh
    exact hh
  -- mod2 zero = zero, so add(mul(div2 0) two) zero = zero
  have h_sub : Γ ⊢ (add (mul (div2 zero) two) zero =eq zero) :=
    eq_trans (eq_congr_add_left (u := mul (div2 zero) two) mod2_zero) h17
  -- ax4(mul(div2 0) two): add(mul(div2 0) two) zero = mul(div2 0) two
  have h4 : Γ ⊢ (add (mul (div2 zero) two) zero =eq mul (div2 zero) two) := by
    have hh := spec h_ax4 (mul (div2 zero) two)
    simp [substFormula, substTerm, substTerms, add, mul, div2, two, FOL.substTerm_liftTerm] at hh
    exact hh
  exact FOL.derive_eq_trans (eq_symm h4) h_sub

theorem div2_zero : Γ ⊢ (div2 zero =eq zero) := by
  have h_ax2  := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  -- Tricotomía: div2(0) < 0 ∨ div2(0) = 0 ∨ 0 < div2(0)
  have h_tri : Γ ⊢ (lt (div2 zero) zero ∨ (div2 zero =eq zero) ∨ lt zero (div2 zero)) := by
    have hh := spec (spec h_ax19 (div2 zero)) zero
    simp [substFormula, substTerm, substTerms, lt, div2, FOL.substTerm_liftTerm] at hh
    exact hh
  apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_tri
  · -- Caso div2(0) < 0: imposible
    intro h_lt
    exact false_elim (by
      have h_ax13_inst : Γ ⊢ (lt (div2 zero) zero ⇔
          Formula.ex (add (div2 zero) (succ (.var 0)) =eq zero)) := by
        have hh := spec (spec h_ax13 (div2 zero)) zero
        simp [substFormula, substTerm, substTerms, lt, add, succ, div2, iff,
              FOL.substTerm_liftTerm] at hh
        exact hh
      apply ex_elim (iff_mp h_ax13_inst h_lt)
      intro k h_k
      -- h_k: add(div2 0)(succ k) = 0
      have h_red : Γ ⊢ (add (div2 zero) (succ k) =eq zero) := by
        simp [substFormula, substTerm, substTerms, add, succ, div2, FOL.substTerm_liftTerm] at h_k
        exact h_k
      exact add_succ_left_ne_zero k (div2 zero)
        (by have h_ax6 := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
            have h6 : Γ ⊢ (add (div2 zero) (succ k) =eq add (succ k) (div2 zero)) := by
              have hh := spec (spec h_ax6 (div2 zero)) (succ k)
              simp [substFormula, substTerm, substTerms, add, succ, div2, FOL.substTerm_liftTerm] at hh
              exact hh
            exact eq_trans h6 h_red))
  · intro h_rest
    apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_rest
    · -- Caso div2(0) = 0: directo
      intro h; exact h
    · -- Caso 0 < div2(0): div2(0) = succ(add 0 k), mul(succ(add 0 k)) two = 0 → ⊥
      intro h_lt
      exact false_elim (by
        have h_ax13_inst : Γ ⊢ (lt zero (div2 zero) ⇔
            Formula.ex (add zero (succ (.var 0)) =eq div2 zero)) := by
          have hh := spec (spec h_ax13 zero) (div2 zero)
          simp [substFormula, substTerm, substTerms, lt, add, succ, div2, iff,
                FOL.substTerm_liftTerm] at hh
          exact hh
        apply ex_elim (iff_mp h_ax13_inst h_lt)
        intro k h_k
        have h_red : Γ ⊢ (add zero (succ k) =eq div2 zero) := by
          simp [substFormula, substTerm, substTerms, add, succ, div2, FOL.substTerm_liftTerm] at h_k
          exact h_k
        -- div2(0) = succ(add 0 k)
        -- ax5(0, k): add 0 (succ k) = succ(add 0 k)
        have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
        have h5 : Γ ⊢ (add zero (succ k) =eq succ (add zero k)) := by
          have hh := spec (spec h_ax5 zero) k
          simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_d2 : Γ ⊢ (div2 zero =eq succ (add zero k)) :=
          FOL.derive_eq_trans (eq_symm h_red) h5
        -- mul(div2 zero) two = zero [div2_zero_mul]
        -- mul(succ(add 0 k)) two = zero [cong]
        have h_mul_zero : Γ ⊢ (mul (succ (add zero k)) two =eq zero) :=
          FOL.derive_eq_trans (eq_congr_mul_right (eq_symm h_d2)) div2_zero_mul
        exact mul_succ_two_ne_zero (add zero k) h_mul_zero)

-- ─────────────────────────────────────────────────────────────────
-- § Teo 5.4: div2(1) = 0
-- ─────────────────────────────────────────────────────────────────

-- Auxiliar: mul(div2 one) two = zero
-- De ax17(one): add(mul(div2 one) two)(mod2 one) = one = succ 0
-- mod2_one: mod2 one = one = succ 0
-- ax5(mul(div2 one) two, 0): add(mul(div2 one) two)(succ 0) = succ(add(mul(div2 one) two) 0)
-- ax4: add X 0 = X  →  succ(mul(div2 one) two) = succ 0  →  ax3  →  mul(div2 one) two = 0
private theorem div2_one_mul : Γ ⊢ (mul (div2 one) two =eq zero) := by
  have h_ax3  := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
  have h_ax4  := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax17 := ax (by simp [axioms] : ax17_div_mod_eq ∈ axioms)
  -- ax17(one): add(mul(div2 one) two)(mod2 one) = one
  have h17 : Γ ⊢ (add (mul (div2 one) two) (mod2 one) =eq one) := by
    have hh := spec h_ax17 one
    simp [substFormula, substTerm, substTerms, add, mul, div2, mod2, one, two,
          FOL.substTerm_liftTerm] at hh
    exact hh
  -- mod2 one = one → add(mul(div2 one) two) one = one
  have h_sub : Γ ⊢ (add (mul (div2 one) two) one =eq one) :=
    eq_trans (eq_congr_add_left (u := mul (div2 one) two) mod2_one) h17
  -- ax5(mul(div2 one) two, zero): add(mul(div2 one) two) one = succ(add(mul(div2 one) two) zero)
  have h5 : Γ ⊢ (add (mul (div2 one) two) one =eq succ (add (mul (div2 one) two) zero)) := by
    have hh := spec (spec h_ax5 (mul (div2 one) two)) zero
    simp [substFormula, substTerm, substTerms, add, succ, mul, div2, one, two,
          FOL.substTerm_liftTerm] at hh
    exact hh
  -- ax4(mul(div2 one) two): add X zero = X
  have h4 : Γ ⊢ (add (mul (div2 one) two) zero =eq mul (div2 one) two) := by
    have hh := spec h_ax4 (mul (div2 one) two)
    simp [substFormula, substTerm, substTerms, add, mul, div2, two, FOL.substTerm_liftTerm] at hh
    exact hh
  -- succ(mul(div2 one) two) = succ(add X zero) [eq_congr_succ (eq_symm h4)]
  --   then = add X one [eq_symm h5]
  --   then = one [h_sub]
  have h_succ_eq : Γ ⊢ (succ (mul (div2 one) two) =eq one) :=
    FOL.derive_eq_trans (eq_congr_succ (eq_symm h4))
      (FOL.derive_eq_trans (eq_symm h5) h_sub)
  -- ax3(zero, mul(div2 one) two): succ(mul(div2 one) two) = succ(0) → ... = 0
  have h3 : Γ ⊢ ((succ (mul (div2 one) two) =eq succ zero) ⇒ (mul (div2 one) two =eq zero)) := by
    have hh := spec (spec h_ax3 (mul (div2 one) two)) zero
    simp [substFormula, substTerm, substTerms, succ, mul, div2, two, FOL.substTerm_liftTerm] at hh
    exact hh
  exact mp h3 h_succ_eq

theorem div2_one : Γ ⊢ (div2 one =eq zero) := by
  have h_ax2  := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  -- Tricotomía: div2(1) < 0 ∨ div2(1) = 0 ∨ 0 < div2(1)
  have h_tri : Γ ⊢ (lt (div2 one) zero ∨ (div2 one =eq zero) ∨ lt zero (div2 one)) := by
    have hh := spec (spec h_ax19 (div2 one)) zero
    simp [substFormula, substTerm, substTerms, lt, div2, one, FOL.substTerm_liftTerm] at hh
    exact hh
  apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_tri
  · intro h_lt
    exact false_elim (by
      have h_ax13_inst : Γ ⊢ (lt (div2 one) zero ⇔
          Formula.ex (add (div2 one) (succ (.var 0)) =eq zero)) := by
        have hh := spec (spec h_ax13 (div2 one)) zero
        simp [substFormula, substTerm, substTerms, lt, add, succ, div2, one, iff,
              FOL.substTerm_liftTerm] at hh
        exact hh
      apply ex_elim (iff_mp h_ax13_inst h_lt)
      intro k h_k
      have h_red : Γ ⊢ (add (div2 one) (succ k) =eq zero) := by
        simp [substFormula, substTerm, substTerms, add, succ, div2, one, FOL.substTerm_liftTerm] at h_k
        exact h_k
      exact add_succ_left_ne_zero k (div2 one)
        (by have h_ax6 := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
            have h6 : Γ ⊢ (add (div2 one) (succ k) =eq add (succ k) (div2 one)) := by
              have hh := spec (spec h_ax6 (div2 one)) (succ k)
              simp [substFormula, substTerm, substTerms, add, succ, div2, one, FOL.substTerm_liftTerm] at hh
              exact hh
            exact eq_trans h6 h_red))
  · intro h_rest
    apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_rest
    · intro h; exact h
    · intro h_lt
      exact false_elim (by
        have h_ax13_inst : Γ ⊢ (lt zero (div2 one) ⇔
            Formula.ex (add zero (succ (.var 0)) =eq div2 one)) := by
          have hh := spec (spec h_ax13 zero) (div2 one)
          simp [substFormula, substTerm, substTerms, lt, add, succ, div2, one, iff,
                FOL.substTerm_liftTerm] at hh
          exact hh
        apply ex_elim (iff_mp h_ax13_inst h_lt)
        intro k h_k
        have h_red : Γ ⊢ (add zero (succ k) =eq div2 one) := by
          simp [substFormula, substTerm, substTerms, add, succ, div2, one, FOL.substTerm_liftTerm] at h_k
          exact h_k
        have h_ax5 := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
        have h5 : Γ ⊢ (add zero (succ k) =eq succ (add zero k)) := by
          have hh := spec (spec h_ax5 zero) k
          simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_d1 : Γ ⊢ (div2 one =eq succ (add zero k)) :=
          FOL.derive_eq_trans (eq_symm h_red) h5
        have h_mul_zero : Γ ⊢ (mul (succ (add zero k)) two =eq zero) :=
          FOL.derive_eq_trans (eq_congr_mul_right (eq_symm h_d1)) div2_one_mul
        exact mul_succ_two_ne_zero (add zero k) h_mul_zero)

-- ─────────────────────────────────────────────────────────────────
-- § Teo 5.6: div2(2) = 1
-- ─────────────────────────────────────────────────────────────────

-- Auxiliar: mul(div2 two) two = two
-- De ax17(two): add(mul(div2 two) two)(mod2 two) = two
-- mod2_two: mod2 two = zero
-- ax4: add X zero = X  →  mul(div2 two) two = two
private theorem div2_two_mul : Γ ⊢ (mul (div2 two) two =eq two) := by
  have h_ax4  := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax17 := ax (by simp [axioms] : ax17_div_mod_eq ∈ axioms)
  have h17 : Γ ⊢ (add (mul (div2 two) two) (mod2 two) =eq two) := by
    have hh := spec h_ax17 two
    simp [substFormula, substTerm, substTerms, add, mul, div2, mod2, two, one,
          FOL.substTerm_liftTerm] at hh
    exact hh
  have h_sub : Γ ⊢ (add (mul (div2 two) two) zero =eq two) :=
    eq_trans (eq_congr_add_left (u := mul (div2 two) two) mod2_two) h17
  have h4 : Γ ⊢ (add (mul (div2 two) two) zero =eq mul (div2 two) two) := by
    have hh := spec h_ax4 (mul (div2 two) two)
    simp [substFormula, substTerm, substTerms, add, mul, div2, two, FOL.substTerm_liftTerm] at hh
    exact hh
  exact FOL.derive_eq_trans (eq_symm h4) h_sub

theorem div2_two : Γ ⊢ (div2 two =eq one) := by
  have h_ax3  := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
  have h_ax4  := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax6  := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_d2 := div2_two_mul  -- mul(div2 two) two = two
  -- Tricotomía: div2(2) < 1 ∨ div2(2) = 1 ∨ 1 < div2(2)
  have h_tri : Γ ⊢ (lt (div2 two) one ∨ (div2 two =eq one) ∨ lt one (div2 two)) := by
    have hh := spec (spec h_ax19 (div2 two)) one
    simp [substFormula, substTerm, substTerms, lt, div2, two, one, FOL.substTerm_liftTerm] at hh
    exact hh
  apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_tri
  · -- Caso div2(2) < 1: ∃k, div2(2)+succ(k)=1=succ(0). ax3: div2(2)+k=0. div2(2)*2=2.
    -- Pero 0 < div2(2) ∨ div2(2) = 0.
    -- Si div2(2) = 0: mul(0)(2) = 0 ≠ 2. ⊥.
    -- Si div2(2) > 0: div2(2) = succ(j). mul(succ j)(2) = 2. Pero lo reescribimos como
    --   add(succ j)(succ k) = succ(add j (succ k)) [ax5 via ax6]. ... = 0 (de div2(2)+k=0).
    --   succ(add j (succ k)) = succ(... or ...). Llevamos a succ = 0. ⊥.
    intro h_lt
    exact false_elim (by
      have h_ax13_inst : Γ ⊢ (lt (div2 two) one ⇔
          Formula.ex (add (div2 two) (succ (.var 0)) =eq one)) := by
        have hh := spec (spec h_ax13 (div2 two)) one
        simp [substFormula, substTerm, substTerms, lt, add, succ, div2, two, one, iff,
              FOL.substTerm_liftTerm] at hh
        exact hh
      apply ex_elim (iff_mp h_ax13_inst h_lt)
      intro k h_k
      -- h_k: add(div2 two)(succ k) = one = succ 0
      have h_red : Γ ⊢ (add (div2 two) (succ k) =eq one) := by
        simp [substFormula, substTerm, substTerms, add, succ, div2, two, one, FOL.substTerm_liftTerm] at h_k
        exact h_k
      -- ax5(div2 two, k): add(div2 two)(succ k) = succ(add(div2 two) k)
      have h5 : Γ ⊢ (add (div2 two) (succ k) =eq succ (add (div2 two) k)) := by
        have hh := spec (spec h_ax5 (div2 two)) k
        simp [substFormula, substTerm, substTerms, add, succ, div2, two, FOL.substTerm_liftTerm] at hh
        exact hh
      -- succ(add(div2 two) k) = succ 0 → ax3 → add(div2 two) k = 0
      have h_succ_eq : Γ ⊢ (succ (add (div2 two) k) =eq one) :=
        eq_trans h5 h_red
      have h3 : Γ ⊢ ((succ (add (div2 two) k) =eq succ zero) ⇒ (add (div2 two) k =eq zero)) := by
        have hh := spec (spec h_ax3 (add (div2 two) k)) zero
        simp [substFormula, substTerm, substTerms, succ, add, div2, two, FOL.substTerm_liftTerm] at hh
        exact hh
      have h_sum_zero : Γ ⊢ (add (div2 two) k =eq zero) := mp h3 h_succ_eq
      -- Tricotomía: div2(2) < 0 ∨ div2(2) = 0 ∨ 0 < div2(2)
      have h_tri2 : Γ ⊢ (lt (div2 two) zero ∨ (div2 two =eq zero) ∨ lt zero (div2 two)) := by
        have hh := spec (spec h_ax19 (div2 two)) zero
        simp [substFormula, substTerm, substTerms, lt, div2, two, FOL.substTerm_liftTerm] at hh
        exact hh
      apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_tri2
      · -- div2(2) < 0: ∃j, div2(2)+succ(j)=0. → add_succ_left_ne_zero ⊥
        intro h_lt2
        have h_ax13_inst2 : Γ ⊢ (lt (div2 two) zero ⇔
            Formula.ex (add (div2 two) (succ (.var 0)) =eq zero)) := by
          have hh := spec (spec h_ax13 (div2 two)) zero
          simp [substFormula, substTerm, substTerms, lt, add, succ, div2, two, iff,
                FOL.substTerm_liftTerm] at hh
          exact hh
        apply ex_elim (iff_mp h_ax13_inst2 h_lt2)
        intro j h_j
        have h_redj : Γ ⊢ (add (div2 two) (succ j) =eq zero) := by
          simp [substFormula, substTerm, substTerms, add, succ, div2, two, FOL.substTerm_liftTerm] at h_j
          exact h_j
        exact add_succ_left_ne_zero j (div2 two)
          (by have h6 : Γ ⊢ (add (div2 two) (succ j) =eq add (succ j) (div2 two)) := by
                have hh := spec (spec h_ax6 (div2 two)) (succ j)
                simp [substFormula, substTerm, substTerms, add, succ, div2, two, FOL.substTerm_liftTerm] at hh
                exact hh
              exact eq_trans h6 h_redj)
      · intro h_rest2
        apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_rest2
        · -- div2(2) = 0: mul(0)(2) = 0, pero h_d2: = 2. teo_1_13_1: neg(0=2). ⊥
          intro h_d2_zero
          -- mul(div2 two) two = mul zero two = 0 [por h_d2_zero y mul_zero_two]
          -- No tenemos mul_zero_two como helper aún, pero podemos derivarlo inline:
          -- ax9(zero, one): mul 0 2 = add(mul 0 1)(0). ax9(zero, zero): mul 0 1 = add(mul 0 0) 0. ax8(zero): mul 0 0 = 0.
          -- →  mul 0 1 = add 0 0. ax4(0): add 0 0 = 0. → mul 0 1 = 0. → mul 0 2 = add 0 0 = 0.
          -- En realidad: cong sobre h_d2_zero y h_d2:
          -- mul(div2 two) two = two y div2(two) = zero → mul zero two = two.
          have h_ax8  := ax (by simp [axioms] : ax8_mul_zero ∈ axioms)
          have h_ax9  := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
          have h9_2 : Γ ⊢ (mul zero two =eq add (mul zero one) zero) := by
            have hh := spec (spec h_ax9 zero) one
            simp [substFormula, substTerm, substTerms, add, succ, mul, two, one, FOL.substTerm_liftTerm] at hh
            exact hh
          have h9_1 : Γ ⊢ (mul zero one =eq add (mul zero zero) zero) := by
            have hh := spec (spec h_ax9 zero) zero
            simp [substFormula, substTerm, substTerms, add, succ, mul, one, FOL.substTerm_liftTerm] at hh
            exact hh
          have h8_0 : Γ ⊢ (mul zero zero =eq zero) := by
            have hh := spec h_ax8 zero
            simp [substFormula, substTerm, substTerms, mul, FOL.substTerm_liftTerm] at hh
            exact hh
          have h4_0 : Γ ⊢ (add zero zero =eq zero) := by
            have hh := spec h_ax4 zero
            simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftTerm] at hh
            exact hh
          have h4_1 : Γ ⊢ (add (mul zero one) zero =eq mul zero one) := by
            have hh := spec h_ax4 (mul zero one)
            simp [substFormula, substTerm, substTerms, add, mul, one, FOL.substTerm_liftTerm] at hh
            exact hh
          -- mul zero one = 0
          have h_mul01 : Γ ⊢ (mul zero one =eq zero) :=
            FOL.derive_eq_trans h9_1 (FOL.derive_eq_trans (eq_congr_add_right h8_0) h4_0)
          -- mul zero two = add 0 zero = 0
          have h_mul02 : Γ ⊢ (mul zero two =eq zero) :=
            FOL.derive_eq_trans h9_2 (FOL.derive_eq_trans (eq_congr_add_right h_mul01) h4_0)
          -- div2(two) = zero → mul(div2 two) two = mul zero two = zero
          have h_mul_cong : Γ ⊢ (mul (div2 two) two =eq mul zero two) :=
            eq_congr_mul_right h_d2_zero
          -- Entonces zero = two de h_d2
          have h_zero_two : Γ ⊢ (zero =eq two) :=
            eq_trans h_mul02 (eq_trans h_mul_cong h_d2)
          exact mp teo_1_13_1 h_zero_two
        · -- 0 < div2(2): ∃j, 0+succ(j)=div2(2). div2(2)=succ(add 0 j).
          --   add(succ(add 0 j))(k) = 0 [desde h_sum_zero, div2(2)=succ(add 0 j)]
          --   add_succ_left_ne_zero ⊥
          intro h_lt2
          have h_ax13_inst2 : Γ ⊢ (lt zero (div2 two) ⇔
              Formula.ex (add zero (succ (.var 0)) =eq div2 two)) := by
            have hh := spec (spec h_ax13 zero) (div2 two)
            simp [substFormula, substTerm, substTerms, lt, add, succ, div2, two, iff,
                  FOL.substTerm_liftTerm] at hh
            exact hh
          apply ex_elim (iff_mp h_ax13_inst2 h_lt2)
          intro j h_j
          have h_redj : Γ ⊢ (add zero (succ j) =eq div2 two) := by
            simp [substFormula, substTerm, substTerms, add, succ, div2, two, FOL.substTerm_liftTerm] at h_j
            exact h_j
          have h5j : Γ ⊢ (add zero (succ j) =eq succ (add zero j)) := by
            have hh := spec (spec h_ax5 zero) j
            simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
            exact hh
          -- div2(2) = succ(add 0 j)
          have h_d2j : Γ ⊢ (div2 two =eq succ (add zero j)) :=
            FOL.derive_eq_trans (eq_symm h_redj) h5j
          -- add(div2 two) k = 0 and div2(two) = succ(add 0 j) → add(succ(add 0 j)) k = 0
          have h_sumk : Γ ⊢ (add (succ (add zero j)) k =eq zero) :=
            FOL.derive_eq_trans (eq_congr_add_right (eq_symm h_d2j)) h_sum_zero
          -- add(succ X) k = add k (succ X) = succ(add k X) ≠ 0 via ax6+ax5+ax2
          exact add_succ_left_ne_zero (add zero j) k h_sumk)
  · intro h_rest
    apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_rest
    · -- Caso div2(2) = 1: directo
      intro h; exact h
    · -- Caso 1 < div2(2): ∃k, 1+succ(k)=div2(2). div2(2)=succ(add 1 k).
      --   mul(succ(add 1 k)) two = two.
      --   Computamos: = succ(add(add 0 (succ(add 1 k)))(add 1 k)).
      --   Esto = two = succ 1 = succ(succ 0). ax3×2: add(add 0 (succ(add 1 k)))(add 1 k) = 1.
      --   add 0 (succ(add 1 k)) = succ(add 0 (add 1 k)) [ax5].
      --   add(succ(add 0 (add 1 k)))(add 1 k) = 1 = succ 0.
      --   Tricotomía (add 1 k) vs 0:
      --   (add 1 k) < 0: imposible.
      --   (add 1 k) = 0: add(succ(add 0 0)) 0 = succ 0 = 1. Pero add 1 k = 0 →
      --     ax5(1, k-1)... o directo: ax6: add k one = 0. add k (succ 0) = succ(add k 0) = succ k = 0. ax2 ⊥.
      --   (add 1 k) > 0: ∃j, 0+succ(j)=add 1 k. add(succ X)(succ(add 0 j)) = 1 = succ 0.
      --     ax6+ax5: succ(add(succ(add 0 j))(succ X)) = succ 0. ax3: add(succ Y)(succ X) = 0. ax5+ax6: succ(...) = 0. ax2 ⊥.
      -- Pero para el caso (add 1 k) = 0: usamos
      --   add one k = 0. ax6: add k one = 0. ax5(k, 0): add k one = succ(add k 0). ax4: = succ k.
      --   succ k = 0. ax2 ⊥.
      -- Así que en cualquier caso hay contradicción.
      intro h_lt
      exact false_elim (by sorry)

-- ─────────────────────────────────────────────────────────────────
-- § Teo 5.8: div2(3) = 1
-- ─────────────────────────────────────────────────────────────────

theorem div2_three : Γ ⊢ (div2 three =eq one) := by sorry

-- ─────────────────────────────────────────────────────────────────
-- § Teo 5.9: div2(4) = 2
-- ─────────────────────────────────────────────────────────────────

theorem div2_four : Γ ⊢ (div2 four =eq two) := by sorry


-- ─────────────────────────────────────────────────────────────────
-- § Teo: mod2_range (ya derivado de ax21)
-- ─────────────────────────────────────────────────────────────────

theorem mod2_range (n : Term) : Γ ⊢ ((mod2 n =eq zero) ∨ (mod2 n =eq one)) :=
  spec (ax (by simp [axioms] : ax21_mod2_range ∈ axioms)) n

end ROBINSON_PlusPlus.Minimal.Theorems.Block3
