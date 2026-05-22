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
import FOL.Theorems.Eq
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

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

-- Lema A (privado): liftTerm 1 (liftTerm 0 t) = liftTerm 0 (liftTerm 0 t)
-- Ambas expresiones incrementan TODOS los índices de variable en 2.
-- Para .var n: liftTerm 0 da .var (n+1), liftTerm 1 sobre ese da .var (n+2).
--              liftTerm 0 sobre .var (n+1) también da .var (n+2). ✓
-- Necesario para que substTerm_liftTerm (c=1) pueda eliminar liftTerm 0 (liftTerm 0 a).
mutual
private theorem lift_01_eq_00 (t : Term) :
    liftTerm 1 (liftTerm 0 t) = liftTerm 0 (liftTerm 0 t) := by
  cases t with
  | var n =>
    -- Para n : Nat, el kernel reduce n < 0 = False definitionally
    -- (Nat.ble (n+1) 0 = false por def, ya que n+1 = Nat.succ _).
    -- Ambos lados = .var (n+2). Se cierra por reflexividad.
    rfl
  | func f ts =>
    simp only [liftTerm]
    congr 1
    exact lift_01_eq_00_list ts

private theorem lift_01_eq_00_list (ts : List Term) :
    liftTerms 1 (liftTerms 0 ts) = liftTerms 0 (liftTerms 0 ts) := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
    -- simp [liftTerms] despliega la lista concreta (a diferencia de unfold
    -- que deja el match en la forma stuck para argumentos no-WHNF)
    simp only [liftTerms]
    rw [lift_01_eq_00 t, lift_01_eq_00_list ts']
end

-- Helper theorem for left cancellation on addition.
-- Proof strategy: ax27_add_left_cancel = ∀a∀b∀c, (add a c = add b c) ⇒ a = b.
-- Triple spec introduces liftTerm 0 (liftTerm 0 a) in the type.
-- Using lift_01_eq_00 (Lema A) + FOL.substTerm_liftTerm, simp reduces the type
-- to the desired formula.
theorem add_left_cancel {a b c : Term}
  (h : Γ ⊢ ((add a c) =eq (add b c))) :
    Γ ⊢ (a =eq b) := by
  have h_ax27 := ax (by simp [axioms, ax27_add_left_cancel] : ax27_add_left_cancel ∈ axioms)
  have h_imp : Γ ⊢ ((add a c =eq add b c) ⇒ (a =eq b)) := by
    have h1 := spec h_ax27 a
    have h2 := spec h1 b
    have h3 := spec h2 c
    -- simp (sin only) incluye ite_true, ite_false, aritmética Nat,
    -- necesarias porque substFormula genera "0 + 1", "0 + 1 + 1" en vez de "1", "2".
    -- lift_01_eq_00 convierte liftTerm 0 (liftTerm 0 a) → liftTerm 1 (liftTerm 0 a)
    -- para que substTerm_liftTerm pueda disparar con c=1.
    simp [substFormula, substTerm, substTerms,
          add, add_sym,
          ← lift_01_eq_00,
          FOL.substTerm_liftTerm] at h3
    exact h3
  exact mp h_imp h

-- Inverse functions (constructive definitions)
def w_of_c (c : Term) : Term := sqrt (add (mul eight c) one)
def y_of_c (c : Term) : Term := pred (pred (mul two c)) -- Placeholder, needs subtraction
def x_of_c (c : Term) : Term := pred (w_of_c c) -- Placeholder, needs subtraction

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

-- Conmutatividad de la suma (helper local).
private theorem add_comm_c (a b : Term) : Γ ⊢ (add a b =eq add b a) := by
  have h := spec (spec (ax (by simp [axioms] : ax6_add_comm ∈ axioms)) a) b
  simp [substFormula, substTerm, substTerms, add, liftTerm, liftTerms, FOL.substTerm_liftTerm] at h
  exact h

-- Teo C7: Cantor(x,y,c) ∧ Cantor(x',y',c) ⇒ x=x' ∧ y=y' (Unicidad Proyectiva)
theorem cantor_uniqueness (x y x' y' c : Term) :
    Γ ⊢ land (is_cantor x y c) (is_cantor x' y' c) ⇒ land (x =eq x') (y =eq y') := by
  apply Axioms.imp_intro; intro h_land
  have h_ax28 := ax (by simp [axioms] : ax28_mul_two_cancel ∈ axioms)
  have h_xy : Γ ⊢ (mul two c =eq add (mul (add x y) (succ (add x y))) (mul two y)) :=
    Axioms.and_elim_left h_land
  have h_x'y' : Γ ⊢ (mul two c =eq add (mul (add x' y') (succ (add x' y'))) (mul two y')) :=
    Axioms.and_elim_right h_land
  -- C5 bounds + uniqueness ⇒ x+y = x'+y'
  have h_w  := cantor_bounds h_xy
  have h_w' := cantor_bounds h_x'y'
  have h_w_eq : Γ ⊢ (add x y =eq add x' y') := lemma_C5_unique h_w h_w'
  -- w(w+1) = w'(w'+1)
  have h_W_eq : Γ ⊢ (mul (add x y) (succ (add x y)) =eq mul (add x' y') (succ (add x' y'))) :=
    FOL.derive_eq_trans (eq_congr_mul_right h_w_eq) (eq_congr_mul_left (eq_congr_succ h_w_eq))
  -- W + 2y = W + 2y'
  have h_WW : Γ ⊢ (add (mul (add x y) (succ (add x y))) (mul two y) =eq
      add (mul (add x y) (succ (add x y))) (mul two y')) :=
    FOL.derive_eq_trans (FOL.derive_eq_trans (eq_symm h_xy) h_x'y')
      (eq_congr_add_right (eq_symm h_W_eq))
  -- conmutar + cancelar ⇒ 2y = 2y'
  have h_2y_eq : Γ ⊢ (mul two y =eq mul two y') := by
    have hcomm : Γ ⊢ (add (mul two y) (mul (add x y) (succ (add x y))) =eq
        add (mul two y') (mul (add x y) (succ (add x y)))) :=
      FOL.derive_eq_trans (add_comm_c (mul two y) (mul (add x y) (succ (add x y))))
        (FOL.derive_eq_trans h_WW (add_comm_c (mul (add x y) (succ (add x y))) (mul two y')))
    exact add_left_cancel hcomm
  -- 2y = 2y' ⇒ y = y'
  have h_y_eq : Γ ⊢ (y =eq y') := by
    have h28 : Γ ⊢ ((mul two y =eq mul two y') ⇒ (y =eq y')) := by
      have hh := spec (spec h_ax28 y) y'
      simp [substFormula, substTerm, substTerms, mul, two, one, FOL.substTerm_liftTerm] at hh
      exact hh
    exact mp h28 h_2y_eq
  -- x+y = x'+y ⇒ x = x'
  have h_x_eq : Γ ⊢ (x =eq x') := by
    have h_axy : Γ ⊢ (add x y =eq add x' y) :=
      FOL.derive_eq_trans h_w_eq (eq_congr_add_left (eq_symm h_y_eq))
    exact add_left_cancel h_axy
  exact Axioms.and_intro h_x_eq h_y_eq

end ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7 (
  cantor_surjectivity
  cantor_uniqueness
)
