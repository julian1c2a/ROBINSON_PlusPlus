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
import FOL.Theorems.Eq
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
theorem w_mul_w_plus_one_eq_sq_w_add_w (w : Term) : Γ ⊢ (mul w (succ w) =eq add (sq w) w) := by
  have h_ax9 := ax (by simp [axioms] : ax9_mul_succ ∈ axioms)
  -- Define f3 como la fórmula con (liftTerm 0 w) en posiciones fijas y .var 0 como m
  let f3 : Formula := Formula.eq
    (mul (liftTerm 0 w) (succ (.var 0)))
    (add (mul (liftTerm 0 w) (.var 0)) (liftTerm 0 w))
  -- hS3: reducción de substFormula 0 s f3 = fórmula con s
  have hS3 : ∀ s : Term, substFormula 0 s f3 =
      Formula.eq (mul w (succ s)) (add (mul w s) w) := by
    intro s
    simp only [f3, substFormula, mul, succ, add, substTerm, substTerms,
               FOL.substTerm_liftTerm, if_true]
  -- hbody_eq: reducción del primer spec de ax9 con w al tipo .forall f3
  have hbody_eq : substFormula 0 w
      (.forall (mul (.var 1) (succ (.var 0)) =eq add (mul (.var 1) (.var 0)) (.var 1)))
      = Formula.forall f3 := rfl
  -- Obtenemos ∀m, mul w (succ m) = add (mul w m) w
  have h_forall_f3 : Γ ⊢ Formula.forall f3 := hbody_eq ▸ spec h_ax9 w
  -- Especializamos con m = w y obtenemos la ecuación deseada
  have h_result : Γ ⊢ Formula.eq (mul w (succ w)) (add (mul w w) w) :=
    (hS3 w) ▸ spec h_forall_f3 w
  -- sq w = mul w w por definición
  simp only [sq]
  exact h_result

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
theorem cantor_poly_term1_eq_sq_add (x y : Term) : Γ ⊢ (w_w_plus_1 (add x y) =eq add (sq (add x y)) (add x y)) :=
  w_mul_w_plus_one_eq_sq_w_add_w (add x y)

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
