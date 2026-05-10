/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import ROBINSON_PlusPlus.Minimal.Axioms
import ROBINSON_PlusPlus.Minimal.Theorems.Block1
import ROBINSON_PlusPlus.Minimal.Theorems.Block3

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Minimal.Theorems.Block1
open ROBINSON_PlusPlus.Minimal.Theorems.Block3

namespace ROBINSON_PlusPlus.Minimal.Theorems.Block4

/-!
## BLOQUE IV — FUNCIÓN DE CANTOR
-/

-- The context for all theorems in this system is the set of axioms.
def Γ := axioms

/-!
### Fase 6: Lema de Paridad
-/

-- Helper definition for w*(w+1)
def w_w_plus_1 (w : Term) : Term :=
  mul w (succ w)

-- Teo 6.1: ∀ w, w*(w+1) = w² + w
theorem w_mul_w_plus_one_eq_sq_w_add_w (w : Term) : Γ ⊢ (mul w (succ w) =eq add (sq w) w) := by sorry

-- Teo 6.2: mod2(w) = 0 ⇒ ∃ k, w*(w+1) = 2*k
theorem parity_lemma_case_even (w : Term) : Γ ⊢ (mod2 w =eq zero) ⇒ ex (w_w_plus_1 w =eq mul two (.var 0)) := by sorry

-- Teo 6.3: mod2(w) = 1 ⇒ ∃ k, w*(w+1) = 2*k
theorem parity_lemma_case_odd (w : Term) : Γ ⊢ (mod2 w =eq one) ⇒ ex (w_w_plus_1 w =eq mul two (.var 0)) := by sorry

-- Lema P1: ∀ w, ∃ k, w*(w+1) = 2*k
theorem parity_lemma (w : Term) : Γ ⊢ ex (w_w_plus_1 w =eq mul two (.var 0)) := by sorry

/-!
### Fase 7: Polinomio de Cantor y Totalidad
-/

-- Teo 7.1 (Lema C1): ∀ x,y, (x+y)*(x+y+1) = (x+y)² + (x+y)
theorem cantor_poly_term1_eq_sq_add (x y : Term) : Γ ⊢ (w_w_plus_1 (add x y) =eq add (sq (add x y)) (add x y)) := by sorry

-- Teo 7.2: ∀ x,y, ∃ k, (x+y)*(x+y+1) + 2*y = 2*k
theorem cantor_poly_is_even (x y : Term) : Γ ⊢ ex (cantor_poly x y =eq mul two (.var 0)) := by sorry

-- Teo C2: ∀ x,y, ∃ c, Cantor(x,y,c) (Totalidad)
theorem cantor_totality (x y : Term) : Γ ⊢ ex (is_cantor x y (.var 0)) := by sorry

/-!
### Fase 8: Inyectividad de Cantor
-/

-- Teo C4: Cantor(x,y,c) ∧ Cantor(x,y,c') ⇒ c = c'
theorem cantor_injective_c (x y c c' : Term) : Γ ⊢ land (is_cantor x y c) (is_cantor x y c') ⇒ (c =eq c') := by sorry

end ROBINSON_PlusPlus.Minimal.Theorems.Block4

-- Exports
export ROBINSON_PlusPlus.Minimal.Theorems.Block4 (
  w_mul_w_plus_one_eq_sq_w_add_w
  parity_lemma_case_even
  parity_lemma_case_odd
  parity_lemma
  cantor_poly_term1_eq_sq_add
  cantor_poly_is_even
  cantor_totality
  cantor_injective_c
)
