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
  sorry

-- Teo 4.2: ∀ n, n < (σ(√n))²
theorem lt_succ_sqrt_sq (n : Term) : Γ ⊢ lt n (sq (succ (sqrt n))) := by
  sorry

-- Teo 4.3: n² = 0 ⇒ n = 0
theorem sq_eq_zero_imp_zero (n : Term) : Γ ⊢ ((sq n =eq zero) ⇒ (n =eq zero)) := by
  sorry

-- Teorema (antes Ax 22): a < b ⇒ σ(a) ≤ b
theorem succ_le_of_lt {a b : Term} (h_lt : Γ ⊢ lt a b) : Γ ⊢ ((succ a) ≤ b) := by
  sorry

-- Lema Auxiliar: a ≤ b ∧ c > 0 ⇒ a*c ≤ b*c
private theorem mul_le_mono_right {a b c : Term} (h_le : Γ ⊢ (a ≤ b)) (h_c_pos : Γ ⊢ lt zero c) : Γ ⊢ ((mul a c) ≤ (mul b c)) := by
  sorry

-- Lema Auxiliar: a ≤ b ⇒ a² ≤ b²
private theorem sq_le_mono {a b : Term} (h_le : Γ ⊢ (a ≤ b)) : Γ ⊢ ((sq a) ≤ (sq b)) := by
  sorry -- Depends on mul_le_mono_right.

-- Lemas auxiliares de transitividad
theorem lt_le_trans {a b c : Term} (h_lt : Γ ⊢ lt a b) (h_le : Γ ⊢ (b ≤ c)) : Γ ⊢ lt a c := by
  sorry

theorem le_lt_trans {a b c : Term} (h_le : Γ ⊢ (a ≤ b)) (h_lt : Γ ⊢ lt b c) : Γ ⊢ lt a c := by
  sorry

theorem le_trans {a b c : Term} (h_ab : Γ ⊢ (a ≤ b)) (h_bc : Γ ⊢ (b ≤ c)) : Γ ⊢ (a ≤ c) := by
  sorry

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
