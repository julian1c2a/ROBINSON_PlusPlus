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

-- Teo 5.2: div2(0) = 0
theorem div2_zero : Γ ⊢ (div2 zero =eq zero) := by sorry

-- Teo 5.4: div2(1) = 0
theorem div2_one : Γ ⊢ (div2 one =eq zero) := by sorry

-- Teo 5.6: div2(2) = 1
theorem div2_two : Γ ⊢ (div2 two =eq one) := by sorry

-- Teo 5.8: div2(3) = 1
theorem div2_three : Γ ⊢ (div2 three =eq one) := by sorry

-- Teo 5.9: div2(4) = 2
theorem div2_four : Γ ⊢ (div2 four =eq two) := by sorry

-- Teo 5.10: ∀ n, mod2(n) = 0 ∨ mod2(n) = 1
-- Prueba: es literalmente ax21_mod2_range.
theorem mod2_range : Γ ⊢ ax21_mod2_range :=
  ax (by simp [axioms, ax21_mod2_range])

end ROBINSON_PlusPlus.Minimal.Theorems.Block3

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block3 (
  mod2_zero
  div2_zero
  mod2_one
  div2_one
  mod2_two
  div2_two
  mod2_three
  div2_three
  mod2_four
  div2_four
  mod2_range
)
