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
import FOL.Metamath.Deduction

open FOL.FOL
open FOL.Tactics
open FOL.Theorems
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
theorem mod2_zero : Γ ⊢ mod2 zero =eq zero := by
  -- From Ax 17: (div2(0) * 2) + mod2(0) = 0
  have h_ax17_spec := spec (ax (by simp [axioms, ax17_div_mod_eq])) (t := zero)
  -- From Teo 2.9: a + b = 0 ⇒ a = 0 ∧ b = 0
  let h_teo2_9_spec := spec (spec teo_2_9 (t := mod2 zero)) (t := mul (div2 zero) two)
  have h_conj : Γ ⊢ land (mul (div2 zero) two =eq zero) (mod2 zero =eq zero) := mp h_teo2_9_spec h_ax17_spec
  exact and_elim_right h_conj

-- Teo 5.2: div2(0) = 0
theorem div2_zero : Γ ⊢ div2 zero =eq zero := by
  -- From Ax 17: (div2(0) * 2) + mod2(0) = 0
  have h_ax17_spec := spec (ax (by simp [axioms, ax17_div_mod_eq])) (t := zero)
  -- From Teo 2.9: a + b = 0 ⇒ a = 0 ∧ b = 0
  let h_teo2_9_spec := spec (spec teo_2_9 (t := mod2 zero)) (t := mul (div2 zero) two)
  have h_conj : Γ ⊢ land (mul (div2 zero) two =eq zero) (mod2 zero =eq zero) := mp h_teo2_9_spec h_ax17_spec
  have h_mul_eq_zero : Γ ⊢ mul (div2 zero) two =eq zero := and_elim_left h_conj
  -- From Teo 2.10: a * b = 0 ⇒ a = 0 ∨ b = 0
  let h_teo2_10_spec := spec (spec teo_2_10 (t := two)) (t := div2 zero)
  have h_disj : Γ ⊢ lor (div2 zero =eq zero) (two =eq zero) := mp h_teo2_10_spec h_mul_eq_zero
  -- We know 2 ≠ 0 (from Teo 1.13_1, which is zero ≠ two)
  have h_two_neq_zero : Γ ⊢ neg (two =eq zero) := eq_symm_neg teo_1_13_1
  -- So we can conclude div2(0) = 0
  apply or_elim h_disj
  · intro h_div2_eq_zero
    exact h_div2_eq_zero
  · intro h_two_eq_zero
    exact false_elim (h_two_neq_zero h_two_eq_zero)

end ROBINSON_PlusPlus.Minimal.Theorems.Block3

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block3 (
  mod2_zero
  div2_zero
)
