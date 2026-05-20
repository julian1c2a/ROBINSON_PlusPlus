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
      exact false_elim (by
        -- h_lt: lt one (div2 two)
        -- ax13(one, div2 two): lt 1 (div2 two) ↔ ∃k, add one (succ k) = div2 two
        have h_ax13_inst : Γ ⊢ (lt one (div2 two) ⇔
            Formula.ex (add one (succ (.var 0)) =eq div2 two)) := by
          have hh := spec (spec h_ax13 one) (div2 two)
          simp [substFormula, substTerm, substTerms, lt, add, succ, div2, two, one, iff,
                FOL.substTerm_liftTerm] at hh
          exact hh
        apply ex_elim (iff_mp h_ax13_inst h_lt)
        intro k h_k
        -- h_k: add one (succ k) = div2 two
        have h_red : Γ ⊢ (add one (succ k) =eq div2 two) := by
          simp [substFormula, substTerm, substTerms, add, succ, div2, two, one, FOL.substTerm_liftTerm] at h_k
          exact h_k
        -- ax5(one, k): add one (succ k) = succ(add one k)
        have h5 : Γ ⊢ (add one (succ k) =eq succ (add one k)) := by
          have hh := spec (spec h_ax5 one) k
          simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
          exact hh
        -- div2(two) = succ(add one k)
        have h_d2k : Γ ⊢ (div2 two =eq succ (add one k)) :=
          FOL.derive_eq_trans (eq_symm h_red) h5
        -- mul(succ(add one k)) two = two  [de h_d2 + congr]
        have h_mul_two : Γ ⊢ (mul (succ (add one k)) two =eq two) :=
          FOL.derive_eq_trans (eq_congr_mul_right (eq_symm h_d2k)) h_d2
        -- Calcular mul(succ t) two con t = add one k
        -- ax9(succ t, one): mul(succ t) two = add(mul(succ t) one)(succ t)
        have h9_2 : Γ ⊢ (mul (succ (add one k)) two =eq add (mul (succ (add one k)) one) (succ (add one k))) := by
          have hh := spec (spec (ax (by simp [axioms] : ax9_mul_succ ∈ axioms)) (succ (add one k))) one
          simp [substFormula, substTerm, substTerms, add, succ, mul, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        -- ax9(succ t, zero): mul(succ t) one = add(mul(succ t) zero)(succ t)
        have h9_1 : Γ ⊢ (mul (succ (add one k)) one =eq add (mul (succ (add one k)) zero) (succ (add one k))) := by
          have hh := spec (spec (ax (by simp [axioms] : ax9_mul_succ ∈ axioms)) (succ (add one k))) zero
          simp [substFormula, substTerm, substTerms, add, succ, mul, one, FOL.substTerm_liftTerm] at hh
          exact hh
        -- ax8(succ t): mul(succ t) zero = zero
        have h8 : Γ ⊢ (mul (succ (add one k)) zero =eq zero) := by
          have hh := spec (ax (by simp [axioms] : ax8_mul_zero ∈ axioms)) (succ (add one k))
          simp [substFormula, substTerm, substTerms, succ, add, mul, one, FOL.substTerm_liftTerm] at hh
          exact hh
        -- ax4(zero): add zero zero = zero
        have h4_0 : Γ ⊢ (add zero zero =eq zero) := by
          have hh := spec h_ax4 zero
          simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftTerm] at hh
          exact hh
        -- mul(succ t) one = add zero (succ t) [por h9_1 + congr h8]
        -- ax5(zero, add one k): add zero (succ(add one k)) = succ(add zero (add one k))
        have h5_0t : Γ ⊢ (add zero (succ (add one k)) =eq succ (add zero (add one k))) := by
          have hh := spec (spec h_ax5 zero) (add one k)
          simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
          exact hh
        -- use h_mul_two and h9_2 to get: add(mul(succ t) one)(succ t) = two
        have h_add_eq_two : Γ ⊢ (add (mul (succ (add one k)) one) (succ (add one k)) =eq two) :=
            FOL.derive_eq_trans (eq_symm h9_2) h_mul_two
        -- mul(succ t) one = add zero (succ t) = succ(add zero t)
        have h_mul1_direct : Γ ⊢ (mul (succ (add one k)) one =eq succ (add zero (add one k))) := by
            have step1 : Γ ⊢ (mul (succ (add one k)) one =eq add zero (succ (add one k))) :=
              FOL.derive_eq_trans h9_1 (eq_congr_add_right h8)
            exact FOL.derive_eq_trans step1 h5_0t
        -- add zero (add one k) = add one k [ax4 doesn't work; we need ax6+ax4]
        -- ax6(zero, add one k): add zero (add one k) = add(add one k) zero
        have h6_0t : Γ ⊢ (add zero (add one k) =eq add (add one k) zero) := by
            have hh := spec (spec h_ax6 zero) (add one k)
            simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
            exact hh
        -- ax4(add one k): add(add one k) zero = add one k
        have h4_t : Γ ⊢ (add (add one k) zero =eq add one k) := by
            have hh := spec h_ax4 (add one k)
            simp [substFormula, substTerm, substTerms, add, one, FOL.substTerm_liftTerm] at hh
            exact hh
        -- add zero (add one k) = add one k
        have h_zero_t : Γ ⊢ (add zero (add one k) =eq add one k) :=
            FOL.derive_eq_trans h6_0t h4_t
        -- mul(succ t) one = succ(add one k)
        have h_mul1_succ : Γ ⊢ (mul (succ (add one k)) one =eq succ (add one k)) :=
            FOL.derive_eq_trans h_mul1_direct (eq_congr_succ h_zero_t)
        -- add(succ(add one k))(succ(add one k)) = two  [congr_add_right h_mul1_succ + h_add_eq_two]
        have h_succ_add_eq : Γ ⊢ (add (succ (add one k)) (succ (add one k)) =eq two) :=
            FOL.derive_eq_trans (eq_congr_add_right (eq_symm h_mul1_succ)) h_add_eq_two
        -- ax5(succ(add one k), add one k): add(succ(add one k))(succ(add one k)) = succ(add(succ(add one k))(add one k))
        have h5_ss : Γ ⊢ (add (succ (add one k)) (succ (add one k)) =eq succ (add (succ (add one k)) (add one k))) := by
            have hh := spec (spec h_ax5 (succ (add one k))) (add one k)
            simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
            exact hh
        -- succ(add(succ(add one k))(add one k)) = two = succ one = succ(succ zero)
        have h_succ_eq2 : Γ ⊢ (succ (add (succ (add one k)) (add one k)) =eq two) :=
            FOL.derive_eq_trans (eq_symm h5_ss) h_succ_add_eq
        -- ax3: add(succ(add one k))(add one k) = one
        have h_ax3 := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
        have h3 : Γ ⊢ ((succ (add (succ (add one k)) (add one k)) =eq succ one) ⇒
              (add (succ (add one k)) (add one k) =eq one)) := by
            have hh := spec (spec h_ax3 (add (succ (add one k)) (add one k))) one
            simp [substFormula, substTerm, substTerms, succ, add, one, FOL.substTerm_liftTerm] at hh
            exact hh
        have h_sum_one : Γ ⊢ (add (succ (add one k)) (add one k) =eq one) :=
            mp h3 h_succ_eq2
        -- add one k = succ k  [ax6(one,k) + ax5(k,zero) + ax4(k)]
        -- ax6(one, k): add one k = add k one
        have h6_1k : Γ ⊢ (add one k =eq add k one) := by
            have hh := spec (spec h_ax6 one) k
            simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
            exact hh
        -- ax5(k, zero): add k one = succ(add k zero)
        have h5_k0 : Γ ⊢ (add k one =eq succ (add k zero)) := by
            have hh := spec (spec h_ax5 k) zero
            simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
            exact hh
        -- ax4(k): add k zero = k
        have h4_k : Γ ⊢ (add k zero =eq k) := by
            have hh := spec h_ax4 k
            simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftTerm] at hh
            exact hh
        -- add one k = succ k
        have h_1k_succ : Γ ⊢ (add one k =eq succ k) :=
            FOL.derive_eq_trans h6_1k (FOL.derive_eq_trans h5_k0 (eq_congr_succ h4_k))
        -- add(succ(succ k))(succ k) = one  [congr h_1k_succ in h_sum_one]
        have h_sum2 : Γ ⊢ (add (succ (succ k)) (succ k) =eq one) := by
            have step1 : Γ ⊢ (add (succ (add one k)) (add one k) =eq add (succ (succ k)) (add one k)) :=
              eq_congr_add_right (eq_congr_succ h_1k_succ)
            have step2 : Γ ⊢ (add (succ (succ k)) (add one k) =eq add (succ (succ k)) (succ k)) :=
              eq_congr_add_left (u := succ (succ k)) h_1k_succ
            exact FOL.derive_eq_trans (eq_symm (FOL.derive_eq_trans step1 step2)) h_sum_one
        -- ax5(succ k, k): add(succ k)(succ k) = succ(add(succ k) k)... but we have add(succ(succ k))(succ k)
        -- ax6(succ(succ k), succ k): add(succ(succ k))(succ k) = add(succ k)(succ(succ k))
        -- Or more directly: add_succ_left_ne_zero with a=succ k, b=succ k
        -- add(succ(succ k))(succ k) = one = succ zero → add_succ_left_ne_zero
        have h_ax2 := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
        -- ax5(succ k, k): add(succ(succ k))(succ k) -- wait, ax5 is add x (succ y) = succ(add x y)
        -- So we need ax5(succ k, succ k) ... no, ax5(X, Y): add X (succ Y) = succ(add X Y)
        -- add(succ(succ k))(succ k) = add(succ(succ k))(succ k) -- this IS add X (succ Y) with X=succ(succ k), Y=k
        have h5_ssk : Γ ⊢ (add (succ (succ k)) (succ k) =eq succ (add (succ (succ k)) k)) := by
            have hh := spec (spec h_ax5 (succ (succ k))) k
            simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
            exact hh
        -- succ(add(succ(succ k)) k) = one = succ zero
        have h_succ3 : Γ ⊢ (succ (add (succ (succ k)) k) =eq one) :=
            FOL.derive_eq_trans (eq_symm h5_ssk) h_sum2
        -- ax3: add(succ(succ k)) k = zero
        have h3b : Γ ⊢ ((succ (add (succ (succ k)) k) =eq succ zero) ⇒
              (add (succ (succ k)) k =eq zero)) := by
            have hh := spec (spec h_ax3 (add (succ (succ k)) k)) zero
            simp [substFormula, substTerm, substTerms, succ, add, FOL.substTerm_liftTerm] at hh
            exact hh
        have h_sum3 : Γ ⊢ (add (succ (succ k)) k =eq zero) := mp h3b h_succ3
        -- add_succ_left_ne_zero: add(succ(succ k)) k = 0 → False
        exact add_succ_left_ne_zero (succ k) k h_sum3)

-- ─────────────────────────────────────────────────────────────────
-- § Teo 5.8: div2(3) = 1
-- ─────────────────────────────────────────────────────────────────

-- Auxiliar: mul(div2 three) two = two
-- De ax17(three): add(mul(div2 three) two)(mod2 three) = three
-- mod2_three: mod2 three = one
-- add(mul(div2 three) two) one = three = succ two = succ(succ one) = succ(succ(succ zero))
-- ax5(mul(div2 three) two, zero): add(mul(div2 three) two) one = succ(add(mul(div2 three) two) zero)
-- ax4: add X zero = X → succ(mul(div2 three) two) = succ two → ax3 → mul(div2 three) two = two
private theorem div2_three_mul : Γ ⊢ (mul (div2 three) two =eq two) := by
  have h_ax3  := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
  have h_ax4  := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax17 := ax (by simp [axioms] : ax17_div_mod_eq ∈ axioms)
  -- ax17(three): add(mul(div2 three) two)(mod2 three) = three
  have h17 : Γ ⊢ (add (mul (div2 three) two) (mod2 three) =eq three) := by
    have hh := spec h_ax17 three
    simp [substFormula, substTerm, substTerms, add, mul, div2, mod2, three, two, one,
          FOL.substTerm_liftTerm] at hh
    exact hh
  -- mod2 three = one → add(mul(div2 three) two) one = three
  have h_sub : Γ ⊢ (add (mul (div2 three) two) one =eq three) :=
    eq_trans (eq_congr_add_left (u := mul (div2 three) two) mod2_three) h17
  -- ax5(mul(div2 three) two, zero): add(mul(div2 three) two) one = succ(add(mul(div2 three) two) zero)
  have h5 : Γ ⊢ (add (mul (div2 three) two) one =eq succ (add (mul (div2 three) two) zero)) := by
    have hh := spec (spec h_ax5 (mul (div2 three) two)) zero
    simp [substFormula, substTerm, substTerms, add, succ, mul, div2, three, two, one,
          FOL.substTerm_liftTerm] at hh
    exact hh
  -- ax4(mul(div2 three) two): add X zero = X
  have h4 : Γ ⊢ (add (mul (div2 three) two) zero =eq mul (div2 three) two) := by
    have hh := spec h_ax4 (mul (div2 three) two)
    simp [substFormula, substTerm, substTerms, add, mul, div2, three, two, FOL.substTerm_liftTerm] at hh
    exact hh
  -- succ(mul(div2 three) two) = three = succ two
  have h_succ_eq : Γ ⊢ (succ (mul (div2 three) two) =eq three) :=
    FOL.derive_eq_trans (eq_congr_succ (eq_symm h4))
      (FOL.derive_eq_trans (eq_symm h5) h_sub)
  -- ax3(mul(div2 three) two, two): succ(mul(div2 three) two) = succ two → mul(div2 three) two = two
  have h3 : Γ ⊢ ((succ (mul (div2 three) two) =eq succ two) ⇒ (mul (div2 three) two =eq two)) := by
    have hh := spec (spec h_ax3 (mul (div2 three) two)) two
    simp [substFormula, substTerm, substTerms, succ, mul, div2, three, two, FOL.substTerm_liftTerm] at hh
    exact hh
  exact mp h3 h_succ_eq

theorem div2_three : Γ ⊢ (div2 three =eq one) := by
  have h_ax3  := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
  have h_ax4  := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax6  := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_d3 := div2_three_mul  -- mul(div2 three) two = two
  -- Tricotomía: div2(3) < 1 ∨ div2(3) = 1 ∨ 1 < div2(3)
  have h_tri : Γ ⊢ (lt (div2 three) one ∨ (div2 three =eq one) ∨ lt one (div2 three)) := by
    have hh := spec (spec h_ax19 (div2 three)) one
    simp [substFormula, substTerm, substTerms, lt, div2, three, two, one, FOL.substTerm_liftTerm] at hh
    exact hh
  apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_tri
  · -- Caso div2(3) < 1: ∃k, div2(3)+succ(k) = one. → succ(div2(3)+k) = succ 0 → div2(3)+k = 0.
    -- Sub-tricotomía div2(3) vs zero:
    -- = 0: mul(0)(2) = 0 pero h_d3 = two → 0 = two → teo_1_13_1 ⊥
    -- < 0: add_succ_left_ne_zero ⊥
    -- > 0: div2(3) = succ j, add(succ j) k = 0 → add_succ_left_ne_zero ⊥
    intro h_lt
    exact false_elim (by
      have h_ax13_inst : Γ ⊢ (lt (div2 three) one ⇔
          Formula.ex (add (div2 three) (succ (.var 0)) =eq one)) := by
        have hh := spec (spec h_ax13 (div2 three)) one
        simp [substFormula, substTerm, substTerms, lt, add, succ, div2, three, two, one, iff,
              FOL.substTerm_liftTerm] at hh
        exact hh
      apply ex_elim (iff_mp h_ax13_inst h_lt)
      intro k h_k
      have h_red : Γ ⊢ (add (div2 three) (succ k) =eq one) := by
        simp [substFormula, substTerm, substTerms, add, succ, div2, three, two, one] at h_k
        exact h_k
      -- ax5(div2 three, k): add(div2 three)(succ k) = succ(add(div2 three) k)
      have h5 : Γ ⊢ (add (div2 three) (succ k) =eq succ (add (div2 three) k)) := by
        have hh := spec (spec h_ax5 (div2 three)) k
        simp [substFormula, substTerm, substTerms, add, succ, div2, three, two, FOL.substTerm_liftTerm] at hh
        exact hh
      -- succ(add(div2 three) k) = one = succ zero → ax3 → add(div2 three) k = zero
      have h_succ_eq : Γ ⊢ (succ (add (div2 three) k) =eq one) := eq_trans h5 h_red
      have h3 : Γ ⊢ ((succ (add (div2 three) k) =eq succ zero) ⇒ (add (div2 three) k =eq zero)) := by
        have hh := spec (spec h_ax3 (add (div2 three) k)) zero
        simp [substFormula, substTerm, substTerms, succ, add, div2, three, two, FOL.substTerm_liftTerm] at hh
        exact hh
      have h_sum_zero : Γ ⊢ (add (div2 three) k =eq zero) := mp h3 h_succ_eq
      -- Sub-tricotomía div2(three) vs zero
      have h_tri2 : Γ ⊢ (lt (div2 three) zero ∨ (div2 three =eq zero) ∨ lt zero (div2 three)) := by
        have hh := spec (spec h_ax19 (div2 three)) zero
        simp [substFormula, substTerm, substTerms, lt, div2, three, two, FOL.substTerm_liftTerm] at hh
        exact hh
      apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_tri2
      · intro h_lt2
        have h_ax13_inst2 : Γ ⊢ (lt (div2 three) zero ⇔
            Formula.ex (add (div2 three) (succ (.var 0)) =eq zero)) := by
          have hh := spec (spec h_ax13 (div2 three)) zero
          simp [substFormula, substTerm, substTerms, lt, add, succ, div2, three, two, iff,
                FOL.substTerm_liftTerm] at hh
          exact hh
        apply ex_elim (iff_mp h_ax13_inst2 h_lt2)
        intro j h_j
        have h_redj : Γ ⊢ (add (div2 three) (succ j) =eq zero) := by
          simp [substFormula, substTerm, substTerms, add, succ, div2, three, two] at h_j
          exact h_j
        exact add_succ_left_ne_zero j (div2 three)
          (by have h6 : Γ ⊢ (add (div2 three) (succ j) =eq add (succ j) (div2 three)) := by
                have hh := spec (spec h_ax6 (div2 three)) (succ j)
                simp [substFormula, substTerm, substTerms, add, succ, div2, three, two, FOL.substTerm_liftTerm] at hh
                exact hh
              exact eq_trans h6 h_redj)
      · intro h_rest2
        apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_rest2
        · -- div2(3) = 0: mul(0)(2) = 0 pero h_d3 = two → 0 = two → teo_1_13_1 ⊥
          intro h_d3_zero
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
          have h_mul01 : Γ ⊢ (mul zero one =eq zero) :=
            FOL.derive_eq_trans h9_1 (FOL.derive_eq_trans (eq_congr_add_right h8_0) h4_0)
          have h_mul02 : Γ ⊢ (mul zero two =eq zero) :=
            FOL.derive_eq_trans h9_2 (FOL.derive_eq_trans (eq_congr_add_right h_mul01) h4_0)
          have h_mul_cong : Γ ⊢ (mul (div2 three) two =eq mul zero two) :=
            eq_congr_mul_right h_d3_zero
          have h_zero_two : Γ ⊢ (zero =eq two) :=
            eq_trans h_mul02 (eq_trans h_mul_cong h_d3)
          exact mp teo_1_13_1 h_zero_two
        · -- 0 < div2(3): ∃j, 0+succ(j) = div2(3). div2(3) = succ(add 0 j).
          -- add(succ(add 0 j)) k = 0 → add_succ_left_ne_zero ⊥
          intro h_lt2
          have h_ax13_inst2 : Γ ⊢ (lt zero (div2 three) ⇔
              Formula.ex (add zero (succ (.var 0)) =eq div2 three)) := by
            have hh := spec (spec h_ax13 zero) (div2 three)
            simp [substFormula, substTerm, substTerms, lt, add, succ, div2, three, two, iff,
                  FOL.substTerm_liftTerm] at hh
            exact hh
          apply ex_elim (iff_mp h_ax13_inst2 h_lt2)
          intro j h_j
          have h_redj : Γ ⊢ (add zero (succ j) =eq div2 three) := by
            simp [substFormula, substTerm, substTerms, add, succ, div2, three, two] at h_j
            exact h_j
          have h5j : Γ ⊢ (add zero (succ j) =eq succ (add zero j)) := by
            have hh := spec (spec h_ax5 zero) j
            simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
            exact hh
          have h_d3j : Γ ⊢ (div2 three =eq succ (add zero j)) :=
            FOL.derive_eq_trans (eq_symm h_redj) h5j
          have h_sumk : Γ ⊢ (add (succ (add zero j)) k =eq zero) :=
            FOL.derive_eq_trans (eq_congr_add_right (eq_symm h_d3j)) h_sum_zero
          exact add_succ_left_ne_zero (add zero j) k h_sumk)
  · intro h_rest
    apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_rest
    · -- Caso div2(3) = 1: directo
      intro h; exact h
    · -- Caso 1 < div2(3): idéntico a caso 1 < div2(2) pero con h_d3
      intro h_lt
      exact false_elim (by
        have h_ax13_inst : Γ ⊢ (lt one (div2 three) ⇔
            Formula.ex (add one (succ (.var 0)) =eq div2 three)) := by
          have hh := spec (spec h_ax13 one) (div2 three)
          simp [substFormula, substTerm, substTerms, lt, add, succ, div2, three, two, one, iff,
                FOL.substTerm_liftTerm] at hh
          exact hh
        apply ex_elim (iff_mp h_ax13_inst h_lt)
        intro k h_k
        have h_red : Γ ⊢ (add one (succ k) =eq div2 three) := by
          simp [substFormula, substTerm, substTerms, add, succ, div2, three, two, one] at h_k
          exact h_k
        have h5 : Γ ⊢ (add one (succ k) =eq succ (add one k)) := by
          have hh := spec (spec h_ax5 one) k
          simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_d3k : Γ ⊢ (div2 three =eq succ (add one k)) :=
          FOL.derive_eq_trans (eq_symm h_red) h5
        have h_mul_two : Γ ⊢ (mul (succ (add one k)) two =eq two) :=
          FOL.derive_eq_trans (eq_congr_mul_right (eq_symm h_d3k)) h_d3
        have h9_2 : Γ ⊢ (mul (succ (add one k)) two =eq add (mul (succ (add one k)) one) (succ (add one k))) := by
          have hh := spec (spec (ax (by simp [axioms] : ax9_mul_succ ∈ axioms)) (succ (add one k))) one
          simp [substFormula, substTerm, substTerms, add, succ, mul, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h9_1 : Γ ⊢ (mul (succ (add one k)) one =eq add (mul (succ (add one k)) zero) (succ (add one k))) := by
          have hh := spec (spec (ax (by simp [axioms] : ax9_mul_succ ∈ axioms)) (succ (add one k))) zero
          simp [substFormula, substTerm, substTerms, add, succ, mul, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h8 : Γ ⊢ (mul (succ (add one k)) zero =eq zero) := by
          have hh := spec (ax (by simp [axioms] : ax8_mul_zero ∈ axioms)) (succ (add one k))
          simp [substFormula, substTerm, substTerms, succ, add, mul, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h5_0t : Γ ⊢ (add zero (succ (add one k)) =eq succ (add zero (add one k))) := by
          have hh := spec (spec h_ax5 zero) (add one k)
          simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_add_eq_two : Γ ⊢ (add (mul (succ (add one k)) one) (succ (add one k)) =eq two) :=
          FOL.derive_eq_trans (eq_symm h9_2) h_mul_two
        have h_mul1_direct : Γ ⊢ (mul (succ (add one k)) one =eq succ (add zero (add one k))) := by
          have step1 : Γ ⊢ (mul (succ (add one k)) one =eq add zero (succ (add one k))) :=
            FOL.derive_eq_trans h9_1 (eq_congr_add_right h8)
          exact FOL.derive_eq_trans step1 h5_0t
        have h6_0t : Γ ⊢ (add zero (add one k) =eq add (add one k) zero) := by
          have hh := spec (spec h_ax6 zero) (add one k)
          simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h4_t : Γ ⊢ (add (add one k) zero =eq add one k) := by
          have hh := spec h_ax4 (add one k)
          simp [substFormula, substTerm, substTerms, add, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_zero_t : Γ ⊢ (add zero (add one k) =eq add one k) :=
          FOL.derive_eq_trans h6_0t h4_t
        have h_mul1_succ : Γ ⊢ (mul (succ (add one k)) one =eq succ (add one k)) :=
          FOL.derive_eq_trans h_mul1_direct (eq_congr_succ h_zero_t)
        have h_succ_add_eq : Γ ⊢ (add (succ (add one k)) (succ (add one k)) =eq two) :=
          FOL.derive_eq_trans (eq_congr_add_right (eq_symm h_mul1_succ)) h_add_eq_two
        have h5_ss : Γ ⊢ (add (succ (add one k)) (succ (add one k)) =eq succ (add (succ (add one k)) (add one k))) := by
          have hh := spec (spec h_ax5 (succ (add one k))) (add one k)
          simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_succ_eq2 : Γ ⊢ (succ (add (succ (add one k)) (add one k)) =eq two) :=
          FOL.derive_eq_trans (eq_symm h5_ss) h_succ_add_eq
        have h3 : Γ ⊢ ((succ (add (succ (add one k)) (add one k)) =eq succ one) ⇒
            (add (succ (add one k)) (add one k) =eq one)) := by
          have hh := spec (spec h_ax3 (add (succ (add one k)) (add one k))) one
          simp [substFormula, substTerm, substTerms, succ, add, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_sum_one : Γ ⊢ (add (succ (add one k)) (add one k) =eq one) :=
          mp h3 h_succ_eq2
        have h6_1k : Γ ⊢ (add one k =eq add k one) := by
          have hh := spec (spec h_ax6 one) k
          simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h5_k0 : Γ ⊢ (add k one =eq succ (add k zero)) := by
          have hh := spec (spec h_ax5 k) zero
          simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h4_k : Γ ⊢ (add k zero =eq k) := by
          have hh := spec h_ax4 k
          simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_1k_succ : Γ ⊢ (add one k =eq succ k) :=
          FOL.derive_eq_trans h6_1k (FOL.derive_eq_trans h5_k0 (eq_congr_succ h4_k))
        have h_sum2 : Γ ⊢ (add (succ (succ k)) (succ k) =eq one) := by
          have step1 : Γ ⊢ (add (succ (add one k)) (add one k) =eq add (succ (succ k)) (add one k)) :=
            eq_congr_add_right (eq_congr_succ h_1k_succ)
          have step2 : Γ ⊢ (add (succ (succ k)) (add one k) =eq add (succ (succ k)) (succ k)) :=
            eq_congr_add_left (u := succ (succ k)) h_1k_succ
          exact FOL.derive_eq_trans (eq_symm (FOL.derive_eq_trans step1 step2)) h_sum_one
        have h5_ssk : Γ ⊢ (add (succ (succ k)) (succ k) =eq succ (add (succ (succ k)) k)) := by
          have hh := spec (spec h_ax5 (succ (succ k))) k
          simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_succ3 : Γ ⊢ (succ (add (succ (succ k)) k) =eq one) :=
          FOL.derive_eq_trans (eq_symm h5_ssk) h_sum2
        have h3b : Γ ⊢ ((succ (add (succ (succ k)) k) =eq succ zero) ⇒
            (add (succ (succ k)) k =eq zero)) := by
          have hh := spec (spec h_ax3 (add (succ (succ k)) k)) zero
          simp [substFormula, substTerm, substTerms, succ, add, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_sum3 : Γ ⊢ (add (succ (succ k)) k =eq zero) := mp h3b h_succ3
        exact add_succ_left_ne_zero (succ k) k h_sum3)

-- ─────────────────────────────────────────────────────────────────
-- § Teo 5.9: div2(4) = 2
-- ─────────────────────────────────────────────────────────────────

-- Auxiliar: mul(div2 four) two = four
-- ax17(four): add(mul(div2 four) two)(mod2 four) = four
-- mod2_four: mod2 four = zero → add(mul(div2 four) two) zero = four
-- ax4: add X zero = X → mul(div2 four) two = four
private theorem div2_four_mul : Γ ⊢ (mul (div2 four) two =eq four) := by
  have h_ax4  := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax17 := ax (by simp [axioms] : ax17_div_mod_eq ∈ axioms)
  -- ax17(four): add(mul(div2 four) two)(mod2 four) = four
  have h17 : Γ ⊢ (add (mul (div2 four) two) (mod2 four) =eq four) := by
    have hh := spec h_ax17 four
    simp [substFormula, substTerm, substTerms, add, mul, div2, mod2, four, three, two, one,
          FOL.substTerm_liftTerm] at hh
    exact hh
  -- mod2 four = zero → add(mul(div2 four) two) zero = four
  have h_sub : Γ ⊢ (add (mul (div2 four) two) zero =eq four) :=
    eq_trans (eq_congr_add_left (u := mul (div2 four) two) mod2_four) h17
  -- ax4: add(mul(div2 four) two) zero = mul(div2 four) two
  have h4 : Γ ⊢ (add (mul (div2 four) two) zero =eq mul (div2 four) two) := by
    have hh := spec h_ax4 (mul (div2 four) two)
    simp [substFormula, substTerm, substTerms, add, mul, div2, four, three, two, FOL.substTerm_liftTerm] at hh
    exact hh
  exact FOL.derive_eq_trans (eq_symm h4) h_sub

theorem div2_four : Γ ⊢ (div2 four =eq two) := by
  have h_ax3  := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
  have h_ax4  := ax (by simp [axioms] : ax4_add_zero ∈ axioms)
  have h_ax5  := ax (by simp [axioms] : ax5_add_succ ∈ axioms)
  have h_ax6  := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
  have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_d4 := div2_four_mul  -- mul(div2 four) two = four
  -- Tricotomía: div2(4) < 2 ∨ div2(4) = 2 ∨ 2 < div2(4)
  have h_tri : Γ ⊢ (lt (div2 four) two ∨ (div2 four =eq two) ∨ lt two (div2 four)) := by
    have hh := spec (spec h_ax19 (div2 four)) two
    simp [substFormula, substTerm, substTerms, lt, div2, four, three, two, one, FOL.substTerm_liftTerm] at hh
    exact hh
  apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_tri
  · -- Caso div2(4) < 2: ∃k, div2(4)+succ(k) = two
    -- succ(div2(4)+k) = two = succ one → ax3 → div2(4)+k = one = succ zero
    -- Sub-tricotomía div2(4) vs zero:
    -- = 0: mul(0)(2) = 0 ≠ four → ⊥
    -- < 0: ⊥
    -- > 0: ∃j, div2(4) = succ(succ j) pero div2(4)+k = one = succ zero → add(succ(succ j)) k = succ zero
    --   ax3: add(succ j) k = zero → add_succ_left_ne_zero ⊥
    -- Para = 1: mul(1)(2) = 2 ≠ four → ⊥
    -- Para = succ(succ j): mul(succ(succ j)) two ≥ four (por inducción) → no trivial
    -- Mejor: div2(4) < 2 → div2(4) = 0 ∨ div2(4) = 1
    -- div2(4) = 0 → mul(0)(2) = 0 ≠ four ⊥
    -- div2(4) = 1 → mul(1)(2) = 2 ≠ four ⊥
    intro h_lt
    have h_bot : Γ ⊢ ⊥ := by
      have h_ax13_inst : Γ ⊢ (lt (div2 four) two ⇔
          Formula.ex (add (div2 four) (succ (.var 0)) =eq two)) := by
        have hh := spec (spec h_ax13 (div2 four)) two
        simp [substFormula, substTerm, substTerms, lt, add, succ, div2, four, three, two, one, iff,
              FOL.substTerm_liftTerm] at hh
        exact hh
      apply ex_elim (iff_mp h_ax13_inst h_lt)
      intro k h_k
      have h_red : Γ ⊢ (add (div2 four) (succ k) =eq two) := by
        simp [substFormula, substTerm, substTerms, add, succ, div2, four, three, two, one] at h_k
        exact h_k
      -- ax5(div2 four, k): add(div2 four)(succ k) = succ(add(div2 four) k)
      have h5 : Γ ⊢ (add (div2 four) (succ k) =eq succ (add (div2 four) k)) := by
        have hh := spec (spec h_ax5 (div2 four)) k
        simp [substFormula, substTerm, substTerms, add, succ, div2, four, three, two, FOL.substTerm_liftTerm] at hh
        exact hh
      -- succ(add(div2 four) k) = two = succ one → ax3 → add(div2 four) k = one
      have h_succ_eq : Γ ⊢ (succ (add (div2 four) k) =eq two) := eq_trans h5 h_red
      have h3 : Γ ⊢ ((succ (add (div2 four) k) =eq succ one) ⇒ (add (div2 four) k =eq one)) := by
        have hh := spec (spec h_ax3 (add (div2 four) k)) one
        simp [substFormula, substTerm, substTerms, succ, add, div2, four, three, two, one, FOL.substTerm_liftTerm] at hh
        exact hh
      have h_sum_one : Γ ⊢ (add (div2 four) k =eq one) := mp h3 h_succ_eq
      -- Sub-tricotomía div2(four) vs one
      have h_tri2 : Γ ⊢ (lt (div2 four) one ∨ (div2 four =eq one) ∨ lt one (div2 four)) := by
        have hh := spec (spec h_ax19 (div2 four)) one
        simp [substFormula, substTerm, substTerms, lt, div2, four, three, two, one, FOL.substTerm_liftTerm] at hh
        exact hh
      apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_tri2
      · -- div2(4) < 1: ∃j, div2(4)+succ(j) = one = succ zero → add(div2 four) j = zero
        -- sub-tri vs zero:
        -- = 0: mul(0)(2) = 0 ≠ four ⊥
        -- < 0: ⊥
        -- > 0: succ j' +... ⊥
        intro h_lt2
        have h_ax13_inst2 : Γ ⊢ (lt (div2 four) one ⇔
            Formula.ex (add (div2 four) (succ (.var 0)) =eq one)) := by
          have hh := spec (spec h_ax13 (div2 four)) one
          simp [substFormula, substTerm, substTerms, lt, add, succ, div2, four, three, two, one, iff,
                FOL.substTerm_liftTerm] at hh
          exact hh
        apply ex_elim (iff_mp h_ax13_inst2 h_lt2)
        intro j h_j
        have h_redj : Γ ⊢ (add (div2 four) (succ j) =eq one) := by
          simp [substFormula, substTerm, substTerms, add, succ, div2, four, three, two, one] at h_j
          exact h_j
        -- succ(add(div2 four) j) = one = succ zero → add(div2 four) j = zero
        have h5j : Γ ⊢ (add (div2 four) (succ j) =eq succ (add (div2 four) j)) := by
          have hh := spec (spec h_ax5 (div2 four)) j
          simp [substFormula, substTerm, substTerms, add, succ, div2, four, three, two, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_succ_ej : Γ ⊢ (succ (add (div2 four) j) =eq one) := eq_trans h5j h_redj
        have h3j : Γ ⊢ ((succ (add (div2 four) j) =eq succ zero) ⇒ (add (div2 four) j =eq zero)) := by
          have hh := spec (spec h_ax3 (add (div2 four) j)) zero
          simp [substFormula, substTerm, substTerms, succ, add, div2, four, three, two, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_sum_zero : Γ ⊢ (add (div2 four) j =eq zero) := mp h3j h_succ_ej
        -- Sub-tricotomía div2(four) vs zero
        have h_tri3 : Γ ⊢ (lt (div2 four) zero ∨ (div2 four =eq zero) ∨ lt zero (div2 four)) := by
          have hh := spec (spec h_ax19 (div2 four)) zero
          simp [substFormula, substTerm, substTerms, lt, div2, four, three, two, FOL.substTerm_liftTerm] at hh
          exact hh
        apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_tri3
        · intro h_lt3
          have h_ax13_inst3 : Γ ⊢ (lt (div2 four) zero ⇔
              Formula.ex (add (div2 four) (succ (.var 0)) =eq zero)) := by
            have hh := spec (spec h_ax13 (div2 four)) zero
            simp [substFormula, substTerm, substTerms, lt, add, succ, div2, four, three, two, iff,
                  FOL.substTerm_liftTerm] at hh
            exact hh
          apply ex_elim (iff_mp h_ax13_inst3 h_lt3)
          intro i h_i
          have h_redi : Γ ⊢ (add (div2 four) (succ i) =eq zero) := by
            simp [substFormula, substTerm, substTerms, add, succ, div2, four, three, two] at h_i
            exact h_i
          have h6i : Γ ⊢ (add (div2 four) (succ i) =eq add (succ i) (div2 four)) := by
            have hh := spec (spec h_ax6 (div2 four)) (succ i)
            simp [substFormula, substTerm, substTerms, add, succ, div2, four, three, two, FOL.substTerm_liftTerm] at hh
            exact hh
          exact add_succ_left_ne_zero i (div2 four) (eq_trans h6i h_redi)
        · intro h_rest3
          apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_rest3
          · -- div2(4) = 0: mul(0)(2) = 0 ≠ four ⊥
            intro h_d4_zero
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
            have h_mul01 : Γ ⊢ (mul zero one =eq zero) :=
              FOL.derive_eq_trans h9_1 (FOL.derive_eq_trans (eq_congr_add_right h8_0) h4_0)
            have h_mul02 : Γ ⊢ (mul zero two =eq zero) :=
              FOL.derive_eq_trans h9_2 (FOL.derive_eq_trans (eq_congr_add_right h_mul01) h4_0)
            have h_mul_cong : Γ ⊢ (mul (div2 four) two =eq mul zero two) :=
              eq_congr_mul_right h_d4_zero
            have h_zero_four : Γ ⊢ (zero =eq four) :=
              eq_trans h_mul02 (eq_trans h_mul_cong h_d4)
            -- neg(zero = four): derive inline
            -- zero = four = succ three = succ(succ two) → ax2 → ⊥
            have h_ax2 := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
            have h_neg_0_four : Γ ⊢ (neg (four =eq zero)) := by
              have hh := spec h_ax2 three
              simp [substFormula, substTerm, substTerms, neg, succ, three, two, one, FOL.substTerm_liftTerm] at hh
              exact hh
            exact mp h_neg_0_four (eq_symm h_zero_four)
          · -- 0 < div2(4): ∃j, div2(4) = succ(add 0 j). Then add(succ X) j = zero ⊥
            intro h_lt3
            have h_ax13_inst3 : Γ ⊢ (lt zero (div2 four) ⇔
                Formula.ex (add zero (succ (.var 0)) =eq div2 four)) := by
              have hh := spec (spec h_ax13 zero) (div2 four)
              simp [substFormula, substTerm, substTerms, lt, add, succ, div2, four, three, two, iff,
                    FOL.substTerm_liftTerm] at hh
              exact hh
            apply ex_elim (iff_mp h_ax13_inst3 h_lt3)
            intro i h_i
            have h_redi : Γ ⊢ (add zero (succ i) =eq div2 four) := by
              simp [substFormula, substTerm, substTerms, add, succ, div2, four, three, two] at h_i
              exact h_i
            have h5i : Γ ⊢ (add zero (succ i) =eq succ (add zero i)) := by
              have hh := spec (spec h_ax5 zero) i
              simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
              exact hh
            have h_d4i : Γ ⊢ (div2 four =eq succ (add zero i)) :=
              FOL.derive_eq_trans (eq_symm h_redi) h5i
            -- add(succ(add zero i)) j = zero → ⊥
            have h_sumj : Γ ⊢ (add (succ (add zero i)) j =eq zero) :=
              FOL.derive_eq_trans (eq_congr_add_right (eq_symm h_d4i)) h_sum_zero
            exact add_succ_left_ne_zero (add zero i) j h_sumj
      · intro h_rest2
        apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_rest2
        · -- div2(4) = 1: mul(1)(2) = 2 ≠ four ⊥
          intro h_d4_one
          -- mul(div2 four) two = mul one two = two
          have h_ax8  := ax (by simp [axioms] : ax8_mul_zero ∈ axioms)
          have h_ax9  := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
          have h9_2 : Γ ⊢ (mul one two =eq add (mul one one) one) := by
            have hh := spec (spec h_ax9 one) one
            simp [substFormula, substTerm, substTerms, add, succ, mul, two, one, FOL.substTerm_liftTerm] at hh
            exact hh
          have h9_1 : Γ ⊢ (mul one one =eq add (mul one zero) one) := by
            have hh := spec (spec h_ax9 one) zero
            simp [substFormula, substTerm, substTerms, add, succ, mul, one, FOL.substTerm_liftTerm] at hh
            exact hh
          have h8_1 : Γ ⊢ (mul one zero =eq zero) := by
            have hh := spec h_ax8 one
            simp [substFormula, substTerm, substTerms, mul, one, FOL.substTerm_liftTerm] at hh
            exact hh
          have h_ax6  := ax (by simp [axioms] : ax6_add_comm ∈ axioms)
          have h4_1 : Γ ⊢ (add zero one =eq one) := by
            have h6 : Γ ⊢ (add zero one =eq add one zero) := by
              have hh := spec (spec h_ax6 zero) one
              simp [substFormula, substTerm, substTerms, add, one, FOL.substTerm_liftTerm] at hh
              exact hh
            have h4 : Γ ⊢ (add one zero =eq one) := by
              have hh := spec h_ax4 one
              simp [substFormula, substTerm, substTerms, add, one, FOL.substTerm_liftTerm] at hh
              exact hh
            exact FOL.derive_eq_trans h6 h4
          -- mul one one = add zero one = one
          have h_mul11 : Γ ⊢ (mul one one =eq one) :=
            FOL.derive_eq_trans h9_1 (FOL.derive_eq_trans (eq_congr_add_right h8_1) h4_1)
          -- add one one = succ one = two (ax5(one, zero) + ax4(one))
          have h5_11 : Γ ⊢ (add one (succ zero) =eq succ (add one zero)) := by
            have hh := spec (spec h_ax5 one) zero
            simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
            exact hh
          have h4_10 : Γ ⊢ (add one zero =eq one) := by
            have hh := spec h_ax4 one
            simp [substFormula, substTerm, substTerms, add, one, FOL.substTerm_liftTerm] at hh
            exact hh
          have h_add11 : Γ ⊢ (add one one =eq two) := by
            -- add one one = add one (succ zero) = succ(add one zero) = succ one = two
            have : Γ ⊢ (add one one =eq succ (add one zero)) := by
              have heq : one = succ zero := rfl
              rw [heq]
              exact h5_11
            exact FOL.derive_eq_trans this (eq_congr_succ h4_10)
          -- mul one two = add(mul one one) one = add one one = two
          have h_mul12 : Γ ⊢ (mul one two =eq two) :=
            FOL.derive_eq_trans h9_2 (FOL.derive_eq_trans (eq_congr_add_right h_mul11) h_add11)
          -- mul(div2 four) two = mul one two [cong via h_d4_one]
          have h_mul_cong : Γ ⊢ (mul (div2 four) two =eq mul one two) :=
            eq_congr_mul_right h_d4_one
          -- two = four
          have h_two_four : Γ ⊢ (two =eq four) :=
            eq_trans h_mul12 (eq_trans h_mul_cong h_d4)
          -- two ≠ four: succ(succ zero) = succ(succ(succ(succ zero)))
          -- ax3: succ zero = succ(succ(succ zero)) → ax3: zero = succ(succ zero) → ax2(succ zero) ⊥
          have h_ax2 := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
          have h_ax3 := ax (by simp [axioms] : ax3_peano_succ_inj ∈ axioms)
          have h3a : Γ ⊢ ((succ (succ zero) =eq succ (succ (succ (succ zero)))) ⇒ (succ zero =eq succ (succ (succ zero)))) := by
            have hh := spec (spec h_ax3 (succ zero)) (succ (succ (succ zero)))
            simp [substFormula, substTerm, substTerms, succ, two, one, FOL.substTerm_liftTerm] at hh
            exact hh
          have h3b : Γ ⊢ ((succ zero =eq succ (succ (succ zero))) ⇒ (zero =eq succ (succ zero))) := by
            have hh := spec (spec h_ax3 zero) (succ (succ zero))
            simp [substFormula, substTerm, substTerms, succ, two, one, FOL.substTerm_liftTerm] at hh
            exact hh
          have h3c : Γ ⊢ ((succ zero =eq succ (succ zero)) ⇒ (zero =eq succ zero)) := by
            have hh := spec (spec h_ax3 zero) (succ zero)
            simp [substFormula, substTerm, substTerms, succ, FOL.substTerm_liftTerm] at hh
            exact hh
          have h_neg_0_succ : Γ ⊢ (neg (succ (succ zero) =eq zero)) := by
            have hh := spec h_ax2 (succ zero)
            simp [substFormula, substTerm, substTerms, neg, succ, FOL.substTerm_liftTerm] at hh
            exact hh
          -- four = succ(succ(succ(succ zero))) = succ three = succ(succ two) = succ(succ(succ one)) = succ(succ(succ(succ zero)))
          -- two = succ(succ zero), four = succ(succ(succ(succ zero)))
          -- two = four ↔ succ(succ zero) = succ(succ(succ(succ zero)))
          -- via ax3: succ zero = succ(succ(succ zero)) → succ zero = succ(succ(succ zero))
          -- via ax3: zero = succ(succ zero) → neg(zero = succ zero) →but need zero = succ(succ zero)
          -- Actually: two = succ one = succ(succ zero); four = succ three = succ(succ two) = succ(succ(succ(succ zero)))
          -- h_two_four : succ(succ zero) = succ(succ(succ(succ zero)))
          -- need to show this implies ⊥
          -- Step: succ(succ zero) = succ(succ(succ(succ zero))) → succ zero = succ(succ(succ zero)) [ax3]
          -- → zero = succ(succ zero) [ax3] → succ(succ zero) = zero [eq_symm]
          -- ax2(succ zero): succ(succ zero) ≠ zero ⊥
          have h_two_four_unfold : Γ ⊢ (succ (succ zero) =eq succ (succ (succ (succ zero)))) := by
            -- two = succ one = succ(succ zero), four = succ three = succ(succ(succ(succ zero)))
            show Γ ⊢ (two =eq four)
            exact h_two_four
          have h_step1 : Γ ⊢ (succ zero =eq succ (succ (succ zero))) :=
            mp h3a h_two_four_unfold
          have h_step2 : Γ ⊢ (zero =eq succ (succ zero)) :=
            mp h3b h_step1
          exact mp h_neg_0_succ (eq_symm h_step2)
        · -- 1 < div2(4): ∃k', 1+succ(k') = div2(4). Similar to previous cases. → ⊥
          intro h_lt2
          exact false_elim (by
            have h_ax13_inst2 : Γ ⊢ (lt one (div2 four) ⇔
                Formula.ex (add one (succ (.var 0)) =eq div2 four)) := by
              have hh := spec (spec h_ax13 one) (div2 four)
              simp [substFormula, substTerm, substTerms, lt, add, succ, div2, four, three, two, one, iff,
                    FOL.substTerm_liftTerm] at hh
              exact hh
            apply ex_elim (iff_mp h_ax13_inst2 h_lt2)
            intro k' h_k'
            have h_red' : Γ ⊢ (add one (succ k') =eq div2 four) := by
              simp [substFormula, substTerm, substTerms, add, succ, div2, four, three, two, one] at h_k'
              exact h_k'
            have h5' : Γ ⊢ (add one (succ k') =eq succ (add one k')) := by
              have hh := spec (spec h_ax5 one) k'
              simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
              exact hh
            have h_d4k' : Γ ⊢ (div2 four =eq succ (add one k')) :=
              FOL.derive_eq_trans (eq_symm h_red') h5'
            have h_mul_four : Γ ⊢ (mul (succ (add one k')) two =eq four) :=
              FOL.derive_eq_trans (eq_congr_mul_right (eq_symm h_d4k')) h_d4
            have h9_2' : Γ ⊢ (mul (succ (add one k')) two =eq add (mul (succ (add one k')) one) (succ (add one k'))) := by
              have hh := spec (spec (ax (by simp [axioms] : ax9_mul_succ ∈ axioms)) (succ (add one k'))) one
              simp [substFormula, substTerm, substTerms, add, succ, mul, two, one, FOL.substTerm_liftTerm] at hh
              exact hh
            have h9_1' : Γ ⊢ (mul (succ (add one k')) one =eq add (mul (succ (add one k')) zero) (succ (add one k'))) := by
              have hh := spec (spec (ax (by simp [axioms] : ax9_mul_succ ∈ axioms)) (succ (add one k'))) zero
              simp [substFormula, substTerm, substTerms, add, succ, mul, one, FOL.substTerm_liftTerm] at hh
              exact hh
            have h8' : Γ ⊢ (mul (succ (add one k')) zero =eq zero) := by
              have hh := spec (ax (by simp [axioms] : ax8_mul_zero ∈ axioms)) (succ (add one k'))
              simp [substFormula, substTerm, substTerms, succ, add, mul, one, FOL.substTerm_liftTerm] at hh
              exact hh
            have h5_0t' : Γ ⊢ (add zero (succ (add one k')) =eq succ (add zero (add one k'))) := by
              have hh := spec (spec h_ax5 zero) (add one k')
              simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
              exact hh
            have h_add_eq_four : Γ ⊢ (add (mul (succ (add one k')) one) (succ (add one k')) =eq four) :=
              FOL.derive_eq_trans (eq_symm h9_2') h_mul_four
            have h_mul1_direct' : Γ ⊢ (mul (succ (add one k')) one =eq succ (add zero (add one k'))) := by
              have step1 : Γ ⊢ (mul (succ (add one k')) one =eq add zero (succ (add one k'))) :=
                FOL.derive_eq_trans h9_1' (eq_congr_add_right h8')
              exact FOL.derive_eq_trans step1 h5_0t'
            have h6_0t' : Γ ⊢ (add zero (add one k') =eq add (add one k') zero) := by
              have hh := spec (spec h_ax6 zero) (add one k')
              simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
              exact hh
            have h4_t' : Γ ⊢ (add (add one k') zero =eq add one k') := by
              have hh := spec h_ax4 (add one k')
              simp [substFormula, substTerm, substTerms, add, one, FOL.substTerm_liftTerm] at hh
              exact hh
            have h_zero_t' : Γ ⊢ (add zero (add one k') =eq add one k') :=
              FOL.derive_eq_trans h6_0t' h4_t'
            have h_mul1_succ' : Γ ⊢ (mul (succ (add one k')) one =eq succ (add one k')) :=
              FOL.derive_eq_trans h_mul1_direct' (eq_congr_succ h_zero_t')
            -- add(succ(add one k'))(succ(add one k')) = four
            have h_succ_add_eq' : Γ ⊢ (add (succ (add one k')) (succ (add one k')) =eq four) :=
              FOL.derive_eq_trans (eq_congr_add_right (eq_symm h_mul1_succ')) h_add_eq_four
            -- ax5: add(succ(add one k'))(succ(add one k')) = succ(add(succ(add one k'))(add one k'))
            have h5_ss' : Γ ⊢ (add (succ (add one k')) (succ (add one k')) =eq succ (add (succ (add one k')) (add one k'))) := by
              have hh := spec (spec h_ax5 (succ (add one k'))) (add one k')
              simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
              exact hh
            -- succ(add(succ(add one k'))(add one k')) = four = succ three
            have h_succ_eq4 : Γ ⊢ (succ (add (succ (add one k')) (add one k')) =eq four) :=
              FOL.derive_eq_trans (eq_symm h5_ss') h_succ_add_eq'
            -- ax3: add(succ(add one k'))(add one k') = three
            have h3' : Γ ⊢ ((succ (add (succ (add one k')) (add one k')) =eq succ three) ⇒
                (add (succ (add one k')) (add one k') =eq three)) := by
              have hh := spec (spec h_ax3 (add (succ (add one k')) (add one k'))) three
              simp [substFormula, substTerm, substTerms, succ, add, three, two, one, FOL.substTerm_liftTerm] at hh
              exact hh
            have h_sum_three : Γ ⊢ (add (succ (add one k')) (add one k') =eq three) :=
              mp h3' h_succ_eq4
            -- add one k' = succ k'
            have h6_1k' : Γ ⊢ (add one k' =eq add k' one) := by
              have hh := spec (spec h_ax6 one) k'
              simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
              exact hh
            have h5_k'0 : Γ ⊢ (add k' one =eq succ (add k' zero)) := by
              have hh := spec (spec h_ax5 k') zero
              simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
              exact hh
            have h4_k' : Γ ⊢ (add k' zero =eq k') := by
              have hh := spec h_ax4 k'
              simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftTerm] at hh
              exact hh
            have h_1k'_succ : Γ ⊢ (add one k' =eq succ k') :=
              FOL.derive_eq_trans h6_1k' (FOL.derive_eq_trans h5_k'0 (eq_congr_succ h4_k'))
            -- add(succ(succ k'))(succ k') = three [congr h_1k'_succ in h_sum_three]
            have h_sum2' : Γ ⊢ (add (succ (succ k')) (succ k') =eq three) := by
              have step1 : Γ ⊢ (add (succ (add one k')) (add one k') =eq add (succ (succ k')) (add one k')) :=
                eq_congr_add_right (eq_congr_succ h_1k'_succ)
              have step2 : Γ ⊢ (add (succ (succ k')) (add one k') =eq add (succ (succ k')) (succ k')) :=
                eq_congr_add_left (u := succ (succ k')) h_1k'_succ
              exact FOL.derive_eq_trans (eq_symm (FOL.derive_eq_trans step1 step2)) h_sum_three
            -- ax5: add(succ(succ k'))(succ k') = succ(add(succ(succ k')) k')
            have h5_ssk' : Γ ⊢ (add (succ (succ k')) (succ k') =eq succ (add (succ (succ k')) k')) := by
              have hh := spec (spec h_ax5 (succ (succ k'))) k'
              simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
              exact hh
            -- succ(add(succ(succ k')) k') = three = succ two
            have h_succ3' : Γ ⊢ (succ (add (succ (succ k')) k') =eq three) :=
              FOL.derive_eq_trans (eq_symm h5_ssk') h_sum2'
            -- ax3: add(succ(succ k')) k' = two
            have h3b' : Γ ⊢ ((succ (add (succ (succ k')) k') =eq succ two) ⇒ (add (succ (succ k')) k' =eq two)) := by
              have hh := spec (spec h_ax3 (add (succ (succ k')) k')) two
              simp [substFormula, substTerm, substTerms, succ, add, two, one, FOL.substTerm_liftTerm] at hh
              exact hh
            have h_sum3' : Γ ⊢ (add (succ (succ k')) k' =eq two) := mp h3b' h_succ3'
            -- ax5: add(succ(succ k')) k' = succ(add(succ(succ k'))(succ k'')) where k' = succ k''... no
            -- ax6 + add_succ_left_ne_zero:
            -- add(succ(succ k'))(succ k'') = two  -- but we have k' directly
            -- Need to reduce further: add(succ(succ k')) k' = two = succ one = succ(succ zero)
            -- ax3: succ(add(succ k') ... hmm we have add(succ(succ k')) k' = two
            -- sub-tri k' vs zero:
            have h_tri_k' : Γ ⊢ (lt k' zero ∨ (k' =eq zero) ∨ lt zero k') := by
              have hh := spec (spec h_ax19 k') zero
              simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at hh
              exact hh
            apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_tri_k'
            · intro h_k'_lt_zero
              have h_ax13_k' : Γ ⊢ (lt k' zero ⇔ Formula.ex (add (liftTerm 0 k') (succ (.var 0)) =eq zero)) := by
                have hh := spec (spec h_ax13 k') zero
                simp [substFormula, substTerm, substTerms, lt, add, succ, iff, liftTerm, liftTerms,
                      FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
                exact hh
              apply ex_elim (iff_mp h_ax13_k' h_k'_lt_zero)
              intro m h_m
              simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at h_m
              exact add_succ_left_ne_zero m k' (by
                have h6m := spec (spec h_ax6 k') (succ m)
                simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at h6m
                exact eq_trans h6m h_m)
            · intro h_rest_k'
              apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_rest_k'
              · -- k' = 0: div2 four = succ(add one zero) = two. add two k = one. Sub-tri on k.
                intro h_k'_zero
                -- In both this case and 0<k', we use h_d4k' directly (it holds for any k').
                -- Sub-tri on outer k vs zero:
                have h_triKz : Γ ⊢ (lt k zero ∨ (k =eq zero) ∨ lt zero k) := by
                  have hh := spec (spec h_ax19 k) zero
                  simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at hh
                  exact hh
                have h_bot2 : Γ ⊢ ⊥ := by
                  apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_triKz
                  · intro h_k_lt
                    have h_ax13Kz : Γ ⊢ (lt k zero ⇔ Formula.ex (add (liftTerm 0 k) (succ (.var 0)) =eq zero)) := by
                      have hh := spec (spec h_ax13 k) zero
                      simp [substFormula, substTerm, substTerms, lt, add, succ, iff, liftTerm, liftTerms,
                            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
                      exact hh
                    apply ex_elim (iff_mp h_ax13Kz h_k_lt)
                    intro m h_m
                    simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at h_m
                    exact add_succ_left_ne_zero m k (by
                      have h6m := spec (spec h_ax6 k) (succ m)
                      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at h6m
                      exact eq_trans h6m h_m)
                  · intro h_restKz
                    apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_restKz
                    · -- k = 0: add(div2 four) 0 = div2 four = one → div2 four = one.
                      -- But h_d4k': div2 four = succ(add one k'). h_k'_zero: k' = 0.
                      -- div2 four = succ one = two. two = one → teo_1_11 ⊥
                      intro h_k_zero
                      have h4_d4 : Γ ⊢ (add (div2 four) zero =eq div2 four) := by
                        have hh := spec h_ax4 (div2 four)
                        simp [substFormula, substTerm, substTerms, add, div2, four, three, two, FOL.substTerm_liftTerm] at hh
                        exact hh
                      have h_d4_one2 : Γ ⊢ (div2 four =eq one) :=
                        FOL.derive_eq_trans (eq_symm h4_d4)
                          (FOL.derive_eq_trans (eq_congr_add_left (u := div2 four) (eq_symm h_k_zero)) h_sum_one)
                      -- h_d4k': div2 four = succ(add one k'). k' = 0. succ(add one 0) = succ one = two.
                      have h_add10 : Γ ⊢ (add one zero =eq one) := by
                        have hh := spec h_ax4 one
                        simp [substFormula, substTerm, substTerms, add, one, FOL.substTerm_liftTerm] at hh
                        exact hh
                      have h_d4_two : Γ ⊢ (div2 four =eq two) :=
                        FOL.derive_eq_trans h_d4k'
                          (eq_congr_succ (FOL.derive_eq_trans (eq_congr_add_left (u := one) h_k'_zero) h_add10))
                      -- two = one (from h_d4_two and h_d4_one2)
                      have h_two_one : Γ ⊢ (two =eq one) :=
                        FOL.derive_eq_trans (eq_symm h_d4_two) h_d4_one2
                      -- two = succ one, one = succ zero. two = one → succ one = succ zero → ax3 → one = zero
                      have h3_21 : Γ ⊢ ((succ one =eq succ zero) ⇒ (one =eq zero)) := by
                        have hh := spec (spec h_ax3 one) zero
                        simp [substFormula, substTerm, substTerms, succ, one, FOL.substTerm_liftTerm] at hh
                        exact hh
                      exact mp teo_1_11 (eq_symm (mp h3_21 h_two_one))
                    · -- 0 < k: derive ⊥ directly using div2 four = two and add two k = one
                      intro h_k_gt
                      have h_add10' : Γ ⊢ (add one zero =eq one) := by
                        have hh := spec h_ax4 one
                        simp [substFormula, substTerm, substTerms, add, one, FOL.substTerm_liftTerm] at hh
                        exact hh
                      have h_d4_two' : Γ ⊢ (div2 four =eq two) :=
                        FOL.derive_eq_trans h_d4k'
                          (eq_congr_succ (FOL.derive_eq_trans (eq_congr_add_left (u := one) h_k'_zero) h_add10'))
                      have h_sum_two_k : Γ ⊢ (add two k =eq one) :=
                        FOL.derive_eq_trans (eq_congr_add_right (eq_symm h_d4_two')) h_sum_one
                      have h6_2k' : Γ ⊢ (add two k =eq add k two) := by
                        have hh := spec (spec h_ax6 two) k
                        simp [substFormula, substTerm, substTerms, add, two, one, FOL.substTerm_liftTerm] at hh
                        exact hh
                      have h5_k1' : Γ ⊢ (add k two =eq succ (add k one)) := by
                        have hh := spec (spec h_ax5 k) one
                        simp [substFormula, substTerm, substTerms, add, succ, two, one, FOL.substTerm_liftTerm] at hh
                        exact hh
                      have h5_k0' : Γ ⊢ (add k one =eq succ (add k zero)) := by
                        have hh := spec (spec h_ax5 k) zero
                        simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
                        exact hh
                      have h4_k' : Γ ⊢ (add k zero =eq k) := by
                        have hh := spec h_ax4 k
                        simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftTerm] at hh
                        exact hh
                      have h_two_k_succ' : Γ ⊢ (add two k =eq succ (succ k)) :=
                        FOL.derive_eq_trans h6_2k' (FOL.derive_eq_trans h5_k1'
                          (eq_congr_succ (FOL.derive_eq_trans h5_k0' (eq_congr_succ h4_k'))))
                      have h_ssk_one' : Γ ⊢ (succ (succ k) =eq one) :=
                        FOL.derive_eq_trans (eq_symm h_two_k_succ') h_sum_two_k
                      have h3_ssk' : Γ ⊢ ((succ (succ k) =eq succ zero) ⇒ (succ k =eq zero)) := by
                        have hh := spec (spec h_ax3 (succ k)) zero
                        simp [substFormula, substTerm, substTerms, succ, FOL.substTerm_liftTerm] at hh
                        exact hh
                      have h_sk_zero' : Γ ⊢ (succ k =eq zero) := mp h3_ssk' h_ssk_one'
                      have h_ax2_loc1 := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
                      have h_neg_sk' : Γ ⊢ neg (succ k =eq zero) := by
                        have hh := spec h_ax2_loc1 k
                        simp [substFormula, substTerm, substTerms, neg, succ, FOL.substTerm_liftTerm] at hh
                        exact hh
                      exact mp h_neg_sk' h_sk_zero'
                exact false_elim h_bot2
              · -- 0 < k': have h_d4k' : div2 four = succ(add one k'). Sub-tri on outer k.
                intro h_lt3'
                have h_triK : Γ ⊢ (lt k zero ∨ (k =eq zero) ∨ lt zero k) := by
                  have hh := spec (spec h_ax19 k) zero
                  simp [substFormula, substTerm, substTerms, lt, FOL.substTerm_liftTerm] at hh
                  exact hh
                have h_bot3 : Γ ⊢ ⊥ := by
                  apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_triK
                  · intro h_K_lt
                    have h_ax13K : Γ ⊢ (lt k zero ⇔ Formula.ex (add (liftTerm 0 k) (succ (.var 0)) =eq zero)) := by
                      have hh := spec (spec h_ax13 k) zero
                      simp [substFormula, substTerm, substTerms, lt, add, succ, iff, liftTerm, liftTerms,
                            FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
                      exact hh
                    apply ex_elim (iff_mp h_ax13K h_K_lt)
                    intro m h_m
                    simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at h_m
                    exact add_succ_left_ne_zero m k (by
                      have h6m := spec (spec h_ax6 k) (succ m)
                      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at h6m
                      exact eq_trans h6m h_m)
                  · intro h_restK
                    apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_restK
                    · -- k = 0: add(div2 four) 0 = div2 four = one → div2 four = one.
                      -- But h_d4k': div2 four = succ(add one k') with 0 < k', so div2 four ≥ two → contradiction.
                      -- Actually: div2 four = one and h_d4k': div2 four = succ(add one k') → succ(add one k') = one
                      -- ax3: add one k' = zero. But 0 < k' → k' = succ m → add one (succ m) = succ(...) ≠ 0 ⊥
                      intro h_K_zero
                      have h4_d4 : Γ ⊢ (add (div2 four) zero =eq div2 four) := by
                        have hh := spec h_ax4 (div2 four)
                        simp [substFormula, substTerm, substTerms, add, div2, four, three, two, FOL.substTerm_liftTerm] at hh
                        exact hh
                      have h_d4_one2 : Γ ⊢ (div2 four =eq one) :=
                        FOL.derive_eq_trans (eq_symm h4_d4)
                          (FOL.derive_eq_trans (eq_congr_add_left (u := div2 four) (eq_symm h_K_zero)) h_sum_one)
                      -- succ(add one k') = one → ax3: add one k' = zero
                      have h3_d4 : Γ ⊢ ((succ (add one k') =eq succ zero) ⇒ (add one k' =eq zero)) := by
                        have hh := spec (spec h_ax3 (add one k')) zero
                        simp [substFormula, substTerm, substTerms, succ, add, one, FOL.substTerm_liftTerm] at hh
                        exact hh
                      have h_one_k'_zero : Γ ⊢ (add one k' =eq zero) :=
                        mp h3_d4 (eq_trans h_d4k' h_d4_one2)
                      -- add one k' = zero but add one k' = succ k' ≠ zero (ax2)
                      have h_ax2_loc2 := ax (by simp [axioms] : ax2_peano_succ_neq_zero ∈ axioms)
                      have h_neg_sk'2 : Γ ⊢ neg (succ k' =eq zero) := by
                        have hh := spec h_ax2_loc2 k'
                        simp [substFormula, substTerm, substTerms, neg, succ, FOL.substTerm_liftTerm] at hh
                        exact hh
                      exact mp h_neg_sk'2 (eq_trans h_1k'_succ h_one_k'_zero)
                    · -- 0 < k: derive ⊥ directly from h_d4k', h_sum_one, h_1k'_succ
                      intro h_K_gt
                      have h_sak'_k_one : Γ ⊢ (add (succ (add one k')) k =eq one) :=
                        FOL.derive_eq_trans (eq_congr_add_right (eq_symm h_d4k')) h_sum_one
                      have h6_sk'k : Γ ⊢ (add (succ (add one k')) k =eq add k (succ (add one k'))) := by
                        have hh := spec (spec h_ax6 (succ (add one k'))) k
                        simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
                        exact hh
                      have h5_kak' : Γ ⊢ (add k (succ (add one k')) =eq succ (add k (add one k'))) := by
                        have hh := spec (spec h_ax5 k) (add one k')
                        simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
                        exact hh
                      have h_succ_kak'_one : Γ ⊢ (succ (add k (add one k')) =eq one) :=
                        FOL.derive_eq_trans (eq_symm h5_kak')
                          (FOL.derive_eq_trans (eq_symm h6_sk'k) h_sak'_k_one)
                      have h_kak'_ksk' : Γ ⊢ (add k (add one k') =eq add k (succ k')) :=
                        eq_congr_add_left (u := k) h_1k'_succ
                      have h_succ_ksk'_one : Γ ⊢ (succ (add k (succ k')) =eq one) :=
                        FOL.derive_eq_trans (eq_symm (eq_congr_succ h_kak'_ksk')) h_succ_kak'_one
                      have h3_ksk' : Γ ⊢ ((succ (add k (succ k')) =eq succ zero) ⇒ (add k (succ k') =eq zero)) := by
                        have hh := spec (spec h_ax3 (add k (succ k'))) zero
                        simp [substFormula, substTerm, substTerms, succ, add, FOL.substTerm_liftTerm] at hh
                        exact hh
                      have h_ksk'_zero : Γ ⊢ (add k (succ k') =eq zero) := mp h3_ksk' h_succ_ksk'_one
                      have h6_ksk' : Γ ⊢ (add k (succ k') =eq add (succ k') k) := by
                        have hh := spec (spec h_ax6 k) (succ k')
                        simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
                        exact hh
                      have h_pf_ksk' := FOL.derive_eq_trans (eq_symm h6_ksk') h_ksk'_zero
                      exact add_succ_left_ne_zero k' k h_pf_ksk'
                exact false_elim h_bot3)
    exact false_elim h_bot
  · intro h_rest
    apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_rest
    · -- Caso div2(4) = 2: directo
      intro h; exact h
    · -- Caso 2 < div2(4): ∃k, two+succ(k) = div2(4)
      -- mul(div2(4)) two = mul(succ(succ(add two k))) two = ... ≥ 6 > four. ⊥ (by detailed calc)
      -- More carefully: mul(succ(succ(add two k))) two. Let t = succ(add two k).
      -- mul(succ t) two = add(mul(succ t) one)(succ t) = add(succ t)(succ t) [since mul t 1 = t]
      -- hmm actually need to compute more carefully.
      -- mul(succ(succ X)) two = add(mul(succ(succ X)) one)(succ(succ X))
      --   mul(succ(succ X)) one = add(mul(succ(succ X)) zero)(succ(succ X)) = succ(succ X)
      --   So = add(succ(succ X))(succ(succ X)) = 2*(2+k+2) ...
      -- Simpler: succ(add two k) ≥ two. Add succ k to get succ(succ(succ ...)) ≥ three.
      -- div2(4) = succ(add two k) = succ(succ(add one k)).
      -- mul(succ(succ(add one k))) two = add(succ(succ(add one k)))(succ(succ(add one k))) (by computation like above)
      -- This is ≥ 4 but showing it > 4 requires more work.
      -- Alternatively: from h_d4: mul(div2(4)) two = four.
      -- div2(4) = succ(succ X) where X = add two k... let's say div2(4) = succ(succ m) with m = add two k.
      -- mul(succ(succ m)) two = mul(succ m) two + succ(succ m)? No, mul(succ n)(2) = mul n 2 + n (not exactly).
      -- Actually ax9: mul(succ t) two = add(mul t two)(succ t) [wait: ax9 is mul(succ y) x = add(mul y x)(succ y)]
      -- Wait: check ax9 signature. From session notes: ax9_mul_succ: ∀x y, mul x (succ y) = add(mul x y) x
      -- So mul X (succ Y) = add (mul X Y) X. So mul X two = mul X (succ one) = add(mul X one) X.
      -- mul X one = mul X (succ zero) = add(mul X zero) X = add zero X = X (via ax6+ax4).
      -- So mul X two = add X X = X + X.
      -- For X = succ(succ m): mul(succ(succ m)) two = succ(succ m) + succ(succ m) = 2*(2+m) = 4+2m.
      -- This equals four iff m = 0. But we're in case 2 < div2(4) → div2(4) = succ(add two k) for some k.
      -- If k = 0: div2(4) = succ two = three. mul three two = 6 ≠ 4. ⊥
      -- If k > 0: even larger. But proving "6 ≠ 4" in FOL requires arithmetic.
      -- 6 = succ(succ(succ(succ(succ(succ zero))))) vs four = succ(succ(succ(succ zero))).
      -- succ(succ(...)) = succ(succ(succ(succ zero))) → inj → ... → succ(succ zero) = zero → ⊥ (ax2).
      -- This is doable but long. Let me do the k=0 case (div2(4) = three) and show it's ⊥:
      -- For general k: div2(4) = succ(add two k) = succ(succ(succ (add zero k))) via two = succ(succ zero).
      -- div2(4) ≥ three. mul(three)(two) = 6 ≠ 4. But mul(div2(4)) two = four. So mul(div2(4)) two ≥ 6 > 4. ⊥.
      -- This still requires showing mul(div2(4)) two ≥ 6. Hard in FOL.
      -- Let me instead just use that: from ax5+ax4: mul(succ(add two k)) two = (succ(add two k))+(succ(add two k))
      -- = succ(add (succ(add two k)) (add two k))  [ax5]
      -- = four → add(succ(add two k))(add two k) = three [ax3]
      -- Then: ax5(add two k, ...): succ(add(add two k)(succ ...) ) -- hmm
      -- Let me use: succ(add(succ(add two k))(add two k)) = four = succ three.
      -- ax3: add(succ(add two k))(add two k) = three.
      -- add(succ(add two k))(add two k) = succ(add(add two k)(add two k)) [ax5+ax6... no].
      -- ax5(X, Y): add X (succ Y) = succ(add X Y). Not directly.
      -- add two k = succ(add one k) [ax5].
      -- add(succ(succ(add one k)))(succ(add one k)) = three = succ two.
      -- ax5(succ(succ(add one k)), add one k): succ(add(succ(succ(add one k)))(add one k)) = succ two.
      -- ax3: add(succ(succ(add one k)))(add one k) = two.
      -- add one k = succ k [as before]. add(succ(succ(succ k)))(succ k) = two.
      -- ax5(succ(succ(succ k)), k): succ(add(succ(succ(succ k))) k) = two.
      -- ax3: add(succ(succ(succ k))) k = one.
      -- ax5(succ(succ k), k) [no, succ(succ(succ k))] ...
      -- k sub-tri:
      -- k = 0: add(succ(succ(succ 0))) 0 = ax4 → succ(succ(succ 0)) = succ(succ(succ zero)) = three = one? ⊥ (teo_1_13_3)
      -- k = succ k'': add(succ(succ(succ(succ k'')))(succ k'') = one. Reduce again similarly.
      -- This recurse until k=0 where we get contradiction. Needs induction or at least finite depth.
      -- Given the case 2 < div2(4): ∃k, add two (succ k) = div2(4). So k is finite (Lean variable, not induction).
      -- For any fixed k, we'd need to unfold finitely. But in FOL this needs either an induction principle or
      -- a smarter argument.
      -- Best approach: use add_succ_left_ne_zero repeatedly.
      -- add(succ(succ(succ k))) k = one = succ zero.
      -- ax5: succ(add(succ(succ k)) k) = succ zero. ax3: add(succ(succ k)) k = zero.
      -- → add_succ_left_ne_zero(succ k, k) h ⊥ ✓
      -- Wait! Let me re-read: add(succ(succ(succ k))) k = one.
      -- ax5(succ(succ(succ k)), k-1)? No. ax5 is: add X (succ Y) = succ(add X Y).
      -- We have: add(succ(succ(succ k))) k. This is NOT in the form add X (succ Y) directly unless k = succ k'.
      -- But we can use ax6: add(succ(succ(succ k))) k = add k (succ(succ(succ k))).
      -- Then ax5(k, succ(succ k)): add k (succ(succ(succ k))) = succ(add k (succ(succ k))). Hmm.
      -- Actually: add(succ(succ(succ k))) k = one.
      -- From this: add(succ k)(succ k) = ? We need different form.
      -- Let me just use the explicit structure:
      -- We have: add(succ(succ(succ k))) k = one = succ zero.
      -- Let A = succ(succ k). Add A (succ k) = ? We want add(succ A) k instead.
      -- add(succ A) k where A = succ(succ k). add(succ A) k = add A (succ ?) hmm.
      -- SHORTCUT: add(succ(succ(succ k))) k via ax6 = add k (succ(succ(succ k))).
      -- ax5(k, succ(succ k)): add k (succ(succ(succ k))) = succ(add k (succ(succ k))).
      -- So succ(add k (succ(succ k))) = one = succ zero. ax3: add k (succ(succ k)) = zero.
      -- add_succ_left_ne_zero(succ k, k): needs add(succ(succ k)) k = zero. But we have add k (succ(succ k)) = zero.
      -- Actually add_succ_left_ne_zero(succ k, ?) says add(succ(succ k)) ? = zero → ⊥. Not quite.
      -- But: add k (succ(succ k)) = zero. By ax6: add(succ(succ k)) k = zero.
      -- Then: add_succ_left_ne_zero(succ k, k): add(succ(succ k)) k = zero → ⊥. ✓ !!!
      intro h_lt
      exact false_elim (by
        have h_ax13_inst : Γ ⊢ (lt two (div2 four) ⇔
            Formula.ex (add two (succ (.var 0)) =eq div2 four)) := by
          have hh := spec (spec h_ax13 two) (div2 four)
          simp [substFormula, substTerm, substTerms, lt, add, succ, div2, four, three, two, one, iff,
                FOL.substTerm_liftTerm] at hh
          exact hh
        apply ex_elim (iff_mp h_ax13_inst h_lt)
        intro k h_k
        have h_red : Γ ⊢ (add two (succ k) =eq div2 four) := by
          simp [substFormula, substTerm, substTerms, add, succ, div2, four, three, two, one] at h_k
          exact h_k
        -- div2 four = succ(add two k) = succ(succ(succ(add zero k)))
        -- ax5(two, k): add two (succ k) = succ(add two k)
        have h5 : Γ ⊢ (add two (succ k) =eq succ (add two k)) := by
          have hh := spec (spec h_ax5 two) k
          simp [substFormula, substTerm, substTerms, add, succ, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_d4k : Γ ⊢ (div2 four =eq succ (add two k)) :=
          FOL.derive_eq_trans (eq_symm h_red) h5
        -- mul(succ(add two k)) two = four
        have h_mul_four : Γ ⊢ (mul (succ (add two k)) two =eq four) :=
          FOL.derive_eq_trans (eq_congr_mul_right (eq_symm h_d4k)) h_d4
        -- mul(succ t) two = add(mul(succ t) one)(succ t)  [ax9 with t = add two k]
        have h9_2 : Γ ⊢ (mul (succ (add two k)) two =eq add (mul (succ (add two k)) one) (succ (add two k))) := by
          have hh := spec (spec (ax (by simp [axioms] : ax9_mul_succ ∈ axioms)) (succ (add two k))) one
          simp [substFormula, substTerm, substTerms, add, succ, mul, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        -- mul(succ t) one = succ(add two k) [similar derivation as before: mul t 1 = t for any t]
        have h9_1 : Γ ⊢ (mul (succ (add two k)) one =eq add (mul (succ (add two k)) zero) (succ (add two k))) := by
          have hh := spec (spec (ax (by simp [axioms] : ax9_mul_succ ∈ axioms)) (succ (add two k))) zero
          simp [substFormula, substTerm, substTerms, add, succ, mul, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h8 : Γ ⊢ (mul (succ (add two k)) zero =eq zero) := by
          have hh := spec (ax (by simp [axioms] : ax8_mul_zero ∈ axioms)) (succ (add two k))
          simp [substFormula, substTerm, substTerms, succ, add, mul, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        -- ax6(zero, succ(add two k)): add zero (succ(add two k)) = add(succ(add two k)) zero
        have h6_0 : Γ ⊢ (add zero (succ (add two k)) =eq add (succ (add two k)) zero) := by
          have hh := spec (spec h_ax6 zero) (succ (add two k))
          simp [substFormula, substTerm, substTerms, add, succ, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        -- ax4: add(succ(add two k)) zero = succ(add two k)
        have h4 : Γ ⊢ (add (succ (add two k)) zero =eq succ (add two k)) := by
          have hh := spec h_ax4 (succ (add two k))
          simp [substFormula, substTerm, substTerms, add, succ, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        -- add zero (succ(add two k)) = succ(add two k)
        have h_zero_succ : Γ ⊢ (add zero (succ (add two k)) =eq succ (add two k)) :=
          FOL.derive_eq_trans h6_0 h4
        -- mul(succ t) one = add zero (succ(add two k)) = succ(add two k) [via h9_1 + h8]
        have h5_0t : Γ ⊢ (add zero (succ (add two k)) =eq succ (add zero (add two k))) := by
          have hh := spec (spec h_ax5 zero) (add two k)
          simp [substFormula, substTerm, substTerms, add, succ, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        -- Actually mul(succ t)(1) = add(mul(succ t) zero)(succ t) = add zero (succ t) → ax5
        -- = succ(add zero (add two k)) [by h5_0t applied to h9_1+congr h8]
        have h_mul1_direct : Γ ⊢ (mul (succ (add two k)) one =eq succ (add zero (add two k))) :=
          FOL.derive_eq_trans h9_1 (FOL.derive_eq_trans (eq_congr_add_right h8) h5_0t)
        -- add zero (add two k) = add two k [ax6+ax4]
        have h6_0t2 : Γ ⊢ (add zero (add two k) =eq add (add two k) zero) := by
          have hh := spec (spec h_ax6 zero) (add two k)
          simp [substFormula, substTerm, substTerms, add, succ, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h4_t2 : Γ ⊢ (add (add two k) zero =eq add two k) := by
          have hh := spec h_ax4 (add two k)
          simp [substFormula, substTerm, substTerms, add, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_zero_t2 : Γ ⊢ (add zero (add two k) =eq add two k) :=
          FOL.derive_eq_trans h6_0t2 h4_t2
        -- mul(succ(add two k)) one = succ(add two k)
        have h_mul1_succ : Γ ⊢ (mul (succ (add two k)) one =eq succ (add two k)) :=
          FOL.derive_eq_trans h_mul1_direct (eq_congr_succ h_zero_t2)
        -- add(succ(add two k))(succ(add two k)) = four [congr + h9_2 + h_mul_four]
        have h_2t_four : Γ ⊢ (add (succ (add two k)) (succ (add two k)) =eq four) :=
          FOL.derive_eq_trans (eq_congr_add_right (eq_symm h_mul1_succ))
            (FOL.derive_eq_trans (eq_symm h9_2) h_mul_four)
        -- ax5(succ(add two k), add two k): add(succ(add two k))(succ(add two k)) = succ(add(succ(add two k))(add two k))
        have h5_ss : Γ ⊢ (add (succ (add two k)) (succ (add two k)) =eq succ (add (succ (add two k)) (add two k))) := by
          have hh := spec (spec h_ax5 (succ (add two k))) (add two k)
          simp [substFormula, substTerm, substTerms, add, succ, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        -- succ(add(succ(add two k))(add two k)) = four = succ three
        have h_succ_eq4 : Γ ⊢ (succ (add (succ (add two k)) (add two k)) =eq four) :=
          FOL.derive_eq_trans (eq_symm h5_ss) h_2t_four
        -- ax3: add(succ(add two k))(add two k) = three
        have h3 : Γ ⊢ ((succ (add (succ (add two k)) (add two k)) =eq succ three) ⇒
            (add (succ (add two k)) (add two k) =eq three)) := by
          have hh := spec (spec h_ax3 (add (succ (add two k)) (add two k))) three
          simp [substFormula, substTerm, substTerms, succ, add, three, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_sum_three : Γ ⊢ (add (succ (add two k)) (add two k) =eq three) :=
          mp h3 h_succ_eq4
        -- add two k = succ(add one k) [ax5(one, k): add one (succ k) = ... no]
        -- ax5(two, k-1)? Better: add two k = add (succ one) k.
        -- ax6(two, k): add two k = add k two. ax5(k, one): add k (succ one) = succ(add k one).
        -- add k one = succ(add k zero) [ax5(k, zero)]. ax4: = succ k.
        -- So add two k = add k two = succ(add k one) = succ(succ k).
        -- Wait! add two k: two = succ(succ zero).
        -- Actually: ax5(succ one, k) would give add(succ one)(succ k) = succ(add(succ one) k). Wrong direction.
        -- ax6(two, k): add two k = add k two = add k (succ one) = succ(add k one) [ax5(k, one)] = succ(succ(add k zero)) [ax5(k,zero)] = succ(succ k) [ax4].
        have h6_2k : Γ ⊢ (add two k =eq add k two) := by
          have hh := spec (spec h_ax6 two) k
          simp [substFormula, substTerm, substTerms, add, succ, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h5_k1 : Γ ⊢ (add k two =eq succ (add k one)) := by
          have hh := spec (spec h_ax5 k) one
          simp [substFormula, substTerm, substTerms, add, succ, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h5_k0 : Γ ⊢ (add k one =eq succ (add k zero)) := by
          have hh := spec (spec h_ax5 k) zero
          simp [substFormula, substTerm, substTerms, add, succ, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h4_k : Γ ⊢ (add k zero =eq k) := by
          have hh := spec h_ax4 k
          simp [substFormula, substTerm, substTerms, add, FOL.substTerm_liftTerm] at hh
          exact hh
        -- add two k = succ(succ k)
        have h_2k_succ : Γ ⊢ (add two k =eq succ (succ k)) :=
          FOL.derive_eq_trans h6_2k (FOL.derive_eq_trans h5_k1 (eq_congr_succ (FOL.derive_eq_trans h5_k0 (eq_congr_succ h4_k))))
        -- add(succ(succ(succ k)))(succ(succ k)) = three [congr h_2k_succ in h_sum_three]
        have h_sum_three2 : Γ ⊢ (add (succ (succ (succ k))) (succ (succ k)) =eq three) := by
          have step1 : Γ ⊢ (add (succ (add two k)) (add two k) =eq add (succ (succ (succ k))) (add two k)) :=
            eq_congr_add_right (eq_congr_succ h_2k_succ)
          have step2 : Γ ⊢ (add (succ (succ (succ k))) (add two k) =eq add (succ (succ (succ k))) (succ (succ k))) :=
            eq_congr_add_left (u := succ (succ (succ k))) h_2k_succ
          exact FOL.derive_eq_trans (eq_symm (FOL.derive_eq_trans step1 step2)) h_sum_three
        -- ax5(succ(succ(succ k)), succ k): add(succ(succ(succ k)))(succ(succ k)) = succ(add(succ(succ(succ k)))(succ k))
        have h5_ss2 : Γ ⊢ (add (succ (succ (succ k))) (succ (succ k)) =eq succ (add (succ (succ (succ k))) (succ k))) := by
          have hh := spec (spec h_ax5 (succ (succ (succ k)))) (succ k)
          simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
          exact hh
        -- succ(add(succ(succ(succ k)))(succ k)) = three = succ two
        have h_succ_two : Γ ⊢ (succ (add (succ (succ (succ k))) (succ k)) =eq three) :=
          FOL.derive_eq_trans (eq_symm h5_ss2) h_sum_three2
        -- ax3: add(succ(succ(succ k)))(succ k) = two
        have h3b : Γ ⊢ ((succ (add (succ (succ (succ k))) (succ k)) =eq succ two) ⇒
            (add (succ (succ (succ k))) (succ k) =eq two)) := by
          have hh := spec (spec h_ax3 (add (succ (succ (succ k))) (succ k))) two
          simp [substFormula, substTerm, substTerms, succ, add, two, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_sum_two : Γ ⊢ (add (succ (succ (succ k))) (succ k) =eq two) :=
          mp h3b h_succ_two
        -- ax5(succ(succ(succ k)), k): add(succ(succ(succ k)))(succ k) = succ(add(succ(succ(succ k))) k)
        have h5_ss3 : Γ ⊢ (add (succ (succ (succ k))) (succ k) =eq succ (add (succ (succ (succ k))) k)) := by
          have hh := spec (spec h_ax5 (succ (succ (succ k)))) k
          simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
          exact hh
        -- succ(add(succ(succ(succ k))) k) = two = succ one
        have h_succ_one : Γ ⊢ (succ (add (succ (succ (succ k))) k) =eq two) :=
          FOL.derive_eq_trans (eq_symm h5_ss3) h_sum_two
        -- ax3: add(succ(succ(succ k))) k = one
        have h3c : Γ ⊢ ((succ (add (succ (succ (succ k))) k) =eq succ one) ⇒
            (add (succ (succ (succ k))) k =eq one)) := by
          have hh := spec (spec h_ax3 (add (succ (succ (succ k))) k)) one
          simp [substFormula, substTerm, substTerms, succ, add, one, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_sum_one2 : Γ ⊢ (add (succ (succ (succ k))) k =eq one) := mp h3c h_succ_one
        -- ax6(succ(succ(succ k)), k): add(succ(succ(succ k))) k = add k (succ(succ(succ k)))
        have h6_final : Γ ⊢ (add (succ (succ (succ k))) k =eq add k (succ (succ (succ k)))) := by
          have hh := spec (spec h_ax6 (succ (succ (succ k)))) k
          simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
          exact hh
        -- ax5(k, succ(succ k)): add k (succ(succ(succ k))) = succ(add k (succ(succ k)))
        have h5_final : Γ ⊢ (add k (succ (succ (succ k))) =eq succ (add k (succ (succ k)))) := by
          have hh := spec (spec h_ax5 k) (succ (succ k))
          simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
          exact hh
        -- succ(add k (succ(succ k))) = one = succ zero → ax3: add k (succ(succ k)) = zero
        have h_succ_final : Γ ⊢ (succ (add k (succ (succ k))) =eq one) :=
          FOL.derive_eq_trans (eq_symm h5_final) (FOL.derive_eq_trans (eq_symm h6_final) h_sum_one2)
        have h3d : Γ ⊢ ((succ (add k (succ (succ k))) =eq succ zero) ⇒ (add k (succ (succ k)) =eq zero)) := by
          have hh := spec (spec h_ax3 (add k (succ (succ k)))) zero
          simp [substFormula, substTerm, substTerms, succ, add, FOL.substTerm_liftTerm] at hh
          exact hh
        have h_sum_zero : Γ ⊢ (add k (succ (succ k)) =eq zero) := mp h3d h_succ_final
        -- add k (succ(succ k)) = add(succ(succ k)) k [ax6]
        have h6_z : Γ ⊢ (add k (succ (succ k)) =eq add (succ (succ k)) k) := by
          have hh := spec (spec h_ax6 k) (succ (succ k))
          simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
          exact hh
        -- add(succ(succ k)) k = zero → add_succ_left_ne_zero(succ k, k) ⊥
        exact add_succ_left_ne_zero (succ k) k (eq_trans h6_z h_sum_zero))


-- ─────────────────────────────────────────────────────────────────
-- § Teo: mod2_range (ya derivado de ax21)
-- ─────────────────────────────────────────────────────────────────

theorem mod2_range (n : Term) : Γ ⊢ ((mod2 n =eq zero) ∨ (mod2 n =eq one)) :=
  spec (ax (by simp [axioms] : ax21_mod2_range ∈ axioms)) n

end ROBINSON_PlusPlus.Minimal.Theorems.Block3
