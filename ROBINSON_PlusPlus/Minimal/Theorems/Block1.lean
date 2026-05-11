/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import FOL.FOL
import FOL.Tactics

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block1

open ROBINSON_PlusPlus.Minimal.Axioms

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

-- Local definitions from TuplasFuncionesYListas.md Def 3-4
def three : Term := succ two
def four : Term := succ three

/-!
## BLOQUE I — ARITMÉTICA BÁSICA
### Fase 1: Evaluación de Constantes
-/

-- Teo 1.1: 1 + 0 = 1
-- Prueba: Ax 4 (∀ n, n + 0 = n) con n := 1.
theorem teo_1_1 : Γ ⊢ (add one zero =eq one) := by
  have h_ax4 : Γ ⊢ ax4_add_zero := ax (by simp [axioms, ax4_add_zero])
  exact spec h_ax4 (t := one)

-- Teo 1.2: 0 + 1 = 1
-- Prueba: 0 + 1 = 1 + 0 (Ax 6) y 1 + 0 = 1 (Teo 1.1).
theorem teo_1_2 : Γ ⊢ (add zero one =eq one) := by
  have h_ax6 : Γ ⊢ ax6_add_comm := ax (by simp [axioms, ax6_add_comm])
  let h_spec_m := spec h_ax6 (t := one)
  let h_spec_n := spec h_spec_m (t := zero)
  exact eq_trans h_spec_n teo_1_1

-- Teo 1.3: 1 + 1 = 2
theorem teo_1_3 : Γ ⊢ (add one one =eq two) := by sorry

-- Teo 1.4: 2 + 1 = 3
theorem teo_1_4 : Γ ⊢ (add two one =eq three) := by sorry

-- Teo 1.5: 1 + 2 = 3
theorem teo_1_5 : Γ ⊢ (add one two =eq three) := by sorry

-- Teo 1.6: 3 + 1 = 4
theorem teo_1_6 : Γ ⊢ (add three one =eq four) := by sorry

-- Teo 1.7: 2 + 2 = 4
theorem teo_1_7 : Γ ⊢ (add two two =eq four) := by sorry

-- Teo 1.8: 1 * 1 = 1
theorem teo_1_8 : Γ ⊢ (mul one one =eq one) := by sorry

-- Teo 1.9: 2 * 1 = 2
theorem teo_1_9 : Γ ⊢ (mul two one =eq two) := by sorry

-- Teo 1.10: 2 * 2 = 4
theorem teo_1_10 : Γ ⊢ (mul two two =eq four) := by sorry

-- Teo 1.11: 0 ≠ 1
theorem teo_1_11 : Γ ⊢ neg (zero =eq one) := by sorry

-- Teo 1.12: 1 ≠ 2
theorem teo_1_12 : Γ ⊢ neg (one =eq two) := by sorry

-- Teo 1.13: Desigualdades entre constantes
theorem teo_1_13_1 : Γ ⊢ neg (zero =eq two) := by sorry

theorem teo_1_13_2 : Γ ⊢ neg (zero =eq three) := by sorry

theorem teo_1_13_3 : Γ ⊢ neg (one =eq three) := by sorry

theorem teo_1_13_4 : Γ ⊢ neg (two =eq three) := by sorry


/-!
### Fase 2: Identidades del 0 y del 1
-/

-- Teo 2.1: ∀ n, n + 0 = n
-- Prueba: Ax 4.
theorem teo_2_1 : Γ ⊢ ax4_add_zero :=
  ax (by simp [axioms, ax4_add_zero])

-- Teo 2.2: ∀ n, 0 + n = n
theorem teo_2_2 : Γ ⊢ forall_ (add zero (.var 0) =eq (.var 0)) := by sorry

-- Teo 2.3: ∀ n, n * 0 = 0
-- Prueba: Ax 8.
theorem teo_2_3 : Γ ⊢ ax8_mul_zero :=
  ax (by simp [axioms, ax8_mul_zero])

-- Teo 2.4: ∀ n, 0 * n = 0
theorem teo_2_4 : Γ ⊢ forall_ (mul zero (.var 0) =eq zero) := by sorry

-- Teo 2.5: ∀ n, n * 1 = n
theorem teo_2_5 : Γ ⊢ forall_ (mul (.var 0) one =eq (.var 0)) := by sorry

-- Teo 2.6: ∀ n, 1 * n = n
theorem teo_2_6 : Γ ⊢ forall_ (mul one (.var 0) =eq (.var 0)) := by sorry

-- Teo 2.7: ∀ n, 2 * n = n + n
theorem teo_2_7 : Γ ⊢ forall_ (mul two (.var 0) =eq add (.var 0) (.var 0)) := by sorry

-- Teo 2.8: ∀ n, σ(n) = n + 1
theorem teo_2_8 : Γ ⊢ forall_ (succ (.var 0) =eq add (.var 0) one) := by sorry

-- Teo 3.11 (Predecessor Axiom as Theorem)
theorem teo_3_11 : Γ ⊢ forall_ (neg ((.var 0) =eq zero) ⇒ ex (succ (.var 0) =eq (.var 1))) := by sorry

-- Teo 2.9: a + b = 0 ⇒ a = 0 ∧ b = 0
theorem teo_2_9 : Γ ⊢ forall_2 ( (add (.var 1) (.var 0) =eq zero) ⇒ (land ((.var 1) =eq zero) ((.var 0) =eq zero)) ) := by sorry

-- Teo 2.10: a * b = 0 ⇒ a = 0 ∨ b = 0
theorem teo_2_10 : Γ ⊢ forall_2 ( (mul (.var 1) (.var 0) =eq zero) ⇒ (lor ((.var 1) =eq zero) ((.var 0) =eq zero)) ) := by sorry

-- Teo 2.11: 2 * a = 2 * b ⇒ a = b
theorem teo_2_11 : Γ ⊢ forall_2 ( (mul two (.var 1) =eq mul two (.var 0)) ⇒ ((.var 1) =eq (.var 0)) ) := by sorry

/-!
### Decidibilidad de la Igualdad
-/

/-- Ax20 convertido en teorema: `∀n,m, n=m ∨ ¬(n=m)`.
    Prueba: por tricotomía (ax19), los casos `n<m` y `m<n` producen `¬(n=m)`
    via irreflexividad (ax18) + `eq_subst`; el caso `n=m` es directo. -/
theorem eq_decidable : Γ ⊢ ax20_eq_decidable := by
  -- ax20_eq_decidable = forall_2 (((.var 1) =eq (.var 0)) ∨ ¬(.var 1) =eq (.var 0))
  -- Estrategia:
  --   1. gen para introducir n (var 1) y m (var 0)
  --   2. or_elim sobre ax19 especializado en n, m:
  --      · Caso n < m: si n=m entonces n<n por eq_subst, contradice ax18 → ¬(n=m)
  --      · Caso n = m: or_intro_left directo
  --      · Caso m < n: simétrico al primer caso
  --   3. gen cierra las cuantificaciones
  sorry

end ROBINSON_PlusPlus.Minimal.Theorems.Block1
