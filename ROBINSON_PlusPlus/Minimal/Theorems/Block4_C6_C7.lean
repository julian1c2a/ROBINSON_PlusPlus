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
          liftTerm, liftTerms, add, add_sym,
          ← lift_01_eq_00,
          FOL.substTerm_liftTerm, FOL.substTerms_liftTerms] at h3
    exact h3
  exact mp h_imp h

-- Inverse functions (constructive definitions)
def w_of_c (c : Term) : Term := w_candidate c
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

-- Teo C7: Cantor(x,y,c) ∧ Cantor(x',y',c) ⇒ x=x' ∧ y=y' (Unicidad Proyectiva)
theorem cantor_uniqueness (x y x' y' c : Term) : Γ ⊢ land (is_cantor x y c) (is_cantor x' y' c) ⇒ land (x =eq x') (y =eq y') := by sorry

end ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block4_C6_C7 (
  cantor_surjectivity
  cantor_uniqueness
)
