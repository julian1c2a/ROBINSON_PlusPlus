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

set_option linter.unusedSimpArgs false

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

-- ============================================================================
-- Inverse functions (constructive definitions using `sub` from Axioms.lean)
-- ============================================================================
-- `w_of_c c` recupera el `w` único del Lema C5: w = div2(pred(√(8c+1))).
-- Coincide con `w_candidate` exportado por Block4_C5 (preferir aquel; este
-- alias se mantiene por compatibilidad).
def w_of_c (c : Term) : Term := w_candidate c

-- Dado el `w` de C5 y `k` tal que w(w+1) = 2k (vía `parity_lemma`),
-- definimos `y = c − k`, lo que da 2y = 2c − w(w+1) en el rango b ≤ a por ax29.
-- En la prueba real, `k` se obtiene por `ex_elim (parity_lemma w)`; el alias
-- a continuación es solo notacional para el caso «cerrado» en el que k = div2(w(w+1)).
def y_of_c (c : Term) : Term := sub c (div2 (mul (w_candidate c) (succ (w_candidate c))))
def x_of_c (c : Term) : Term := sub (w_candidate c) (y_of_c c)

-- Teo C6: ∀ c, ∃ x, ∃ y, Cantor(x,y,c) (Sobreyectividad)
-- ESQUEMA DE PRUEBA (infraestructura ahora disponible — pendiente de redacción):
--   1. `cantor_uniqueness` + `lemma_C5 c` ⟹ obtenemos `w` con bounds en `h_w`.
--   2. `parity_lemma w` ⟹ ∃ k, w(w+1) = 2k. ex_elim para nombrar k, h_k.
--   3. Definimos y := sub c k. De ax29_sub_witness con (a := c, b := k):
--        si k ≤ c entonces k + (c − k) = c, i.e. k + y = c, i.e. 2k + 2y = 2c.
--      Para `k ≤ c`: de h_w.lo (w(w+1) ≤ 2c) y h_k (w(w+1) = 2k) ⟹ 2k ≤ 2c,
--      y por `le_of_mul_le_mul_left` (Block4_C5 exportado): k ≤ c.
--   4. Definimos x := sub w y. De ax29 con (a := w, b := y) y «y ≤ w»
--      (que se sigue de 2y < 2(w+1) usando h_w.hi y expand_succ_succ):
--      x + y = w.
--   5. Verificamos `is_cantor x y c`, i.e. 2c =eq (x+y)(x+y+1) + 2y:
--        (x+y)(x+y+1) = w(w+1) = 2k  [usando (4) y h_k]
--        2k + 2y = 2c                [por construcción en (3)]
--   6. `ex_intro x (ex_intro y ...)` cierra (cuidando los lifts en el ∃∃).
--
-- Infraestructura ya disponible para esta prueba:
--   - `lemma_C5`, `cantor_bounds`, `lemma_C5_unique` (Block4_C5)
--   - `parity_lemma` (Block4)
--   - `sub`, `ax29_sub_witness` (Axioms.lean)
--   - `add_left_cancel` (este módulo, ax27)
--   - `le_of_mul_le_mul_left`, `le_mul_left`, `eq_congr_*` (exportados)
theorem cantor_surjectivity (c : Term) : Γ ⊢ ex (ex (is_cantor (.var 1) (.var 0) c)) := by
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
