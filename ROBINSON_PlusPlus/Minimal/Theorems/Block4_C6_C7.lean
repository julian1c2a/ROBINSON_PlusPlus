/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block2
import ROBINSON_PlusPlus.Minimal.Theorems.Block3
import ROBINSON_PlusPlus.Minimal.Theorems.Block4
import ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open FOL.FOL
open FOL.Tactics
open FOL.Theorems
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1
open ROBINSON_PlusPlus.Minimal.Theorems.Block2
open ROBINSON_PlusPlus.Minimal.Theorems.Block3
open ROBINSON_PlusPlus.Minimal.Theorems.Block4
open ROBINSON_PlusPlus.Minimal.Theorems.Block4_C5

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7

/-!
## BLOQUE IV — TEOREMAS C6 Y C7 (SOBREYECTIVIDAD Y UNICIDAD)
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 9.2: Sobreyectividad y Unicidad Proyectiva
-/

-- Helper theorem for left cancellation on addition
theorem add_left_cancel {a b c : Term} (h : Γ ⊢ add a c =eq add b c) : Γ ⊢ a =eq b := by
  have h_ax27 := ax (by simp [axioms, ax27_add_left_cancel])
  exact mp (spec (spec (spec h_ax27 (t := c)) (t := b)) (t := a)) h

-- Inverse functions (constructive definitions)
def w_of_c (c : Term) : Term := (ex1_choose (lemma_C5 c)).val
def y_of_c (c : Term) : Term := tau (tau (mul two c)) -- Placeholder, needs subtraction
def x_of_c (c : Term) : Term := tau (w_of_c c) -- Placeholder, needs subtraction

-- Teo C6: ∀ c, ∃ x, ∃ y, Cantor(x,y,c) (Sobreyectividad)
theorem cantor_surjectivity (c : Term) : Γ ⊢ ex (ex (is_cantor (.var 1) (.var 0) c)) := by
  -- The proof is constructive but highly complex.
  -- 1. Use `lemma_C5` to get the unique `w`.
  -- 2. Define `y` implicitly from `2c = w(w+1) + 2y`. This requires showing `w(w+1) <= 2c`
  --    and that `2c - w(w+1)` is even.
  -- 3. Define `x` implicitly from `w = x+y`.
  -- 4. Verify that `is_cantor x y c` holds.
  -- This proof is a major undertaking and is left as sorry for now.
  sorry

-- Teo C7: Cantor(x,y,c) ∧ Cantor(x',y',c) ⇒ x=x' ∧ y=y' (Unicidad Proyectiva)
theorem cantor_uniqueness (x y x' y' c : Term) : Γ ⊢ land (is_cantor x y c) (is_cantor x' y' c) ⇒ land (x =eq x') (y =eq y') := by
  apply deduction_theorem; intro h_and
  have h_xy : Γ ⊢ is_cantor x y c := and_elim_left h_and
  have h_x'y' : Γ ⊢ is_cantor x' y' c := and_elim_right h_and
  simp [is_cantor] at h_xy h_x'y'

  -- 1. Show that w = x+y and w' = x'+y' must be equal by uniqueness from C5.
  -- This sub-proof is complex and requires showing that `is_cantor` implies the C5 bounds.
  have h_w_eq_w' : Γ ⊢ add x y =eq add x' y' := by sorry

  -- 2. From `2c = (x+y)(x+y+1) + 2y` and `2c = (x'+y')(x'+y'+1) + 2y'`,
  -- and `x+y = x'+y'`, we get `(x+y)(x+y+1) + 2y = (x+y)(x+y+1) + 2y'`.
  have h_poly_xy_eq_poly_x_y : Γ ⊢ cantor_poly x y =eq cantor_poly x' y' := eq_trans h_xy (eq_symm h_x'y')
  simp [cantor_poly] at h_poly_xy_eq_poly_x_y
  have h_step1 : Γ ⊢ add (mul (add x y) (succ (add x y))) (mul two y) =eq add (mul (add x' y') (succ (add x' y'))) (mul two y') := h_poly_xy_eq_poly_x_y
  have h_step2 : Γ ⊢ add (mul (add x y) (succ (add x y))) (mul two y) =eq add (mul (add x y) (succ (add x y))) (mul two y') := by
    rwa [h_w_eq_w'] at h_step1

  -- 3. By left cancellation for addition, `2y = 2y'`.
  have h_2y_eq_2y' : Γ ⊢ mul two y =eq mul two y' := add_left_cancel h_step2

  -- 4. By cancellation for `*2` (Teo 2.11), `y = y'`.
  have h_y_eq_y' : Γ ⊢ y =eq y' := mp (spec (spec teo_2_11 (t := y')) (t := y)) h_2y_eq_2y'

  -- 5. From `x+y = x'+y'` and `y=y'`, by cancellation for addition, `x=x'`.
  have h_x_plus_y_eq_x'_plus_y : Γ ⊢ add x y =eq add x' y := by rwa [h_y_eq_y'] at h_w_eq_w'
  have h_x_eq_x' : Γ ⊢ x =eq x' := add_left_cancel h_x_plus_y_eq_x'_plus_y

  exact and_intro h_x_eq_x' h_y_eq_y'

end ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7 (
  cantor_surjectivity
  cantor_uniqueness
)
