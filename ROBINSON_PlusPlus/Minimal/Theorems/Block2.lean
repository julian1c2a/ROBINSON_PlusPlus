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
  have h_ax14 := ax (by simp [axioms] : ax14_sqrt_le ∈ axioms)
  have h := spec h_ax14 n
  simp only [substFormula, substTerm, substTerms, le, lt, sq, mul, if_true] at h
  exact h

-- Teo 4.2: ∀ n, n < (σ(√n))²
theorem lt_succ_sqrt_sq (n : Term) : Γ ⊢ lt n (sq (succ (sqrt n))) := by
  have h_ax15 := ax (by simp [axioms] : ax15_lt_succ_sqrt ∈ axioms)
  have h := spec h_ax15 n
  simp only [substFormula, substTerm, substTerms, lt, sq, succ, mul, if_true] at h
  exact h

-- Teo 4.3: n² = 0 ⇒ n = 0
theorem sq_eq_zero_imp_zero (n : Term) : Γ ⊢ ((sq n =eq zero) ⇒ (n =eq zero)) := by
  sorry

-- Teorema (antes Ax 22): a < b ⇒ σ(a) ≤ b
-- Prueba siguiendo THOUGHTS.md §"¿Es necesario el axioma 22?"
theorem succ_le_of_lt {a b : Term} (h_lt : Γ ⊢ lt a b) : Γ ⊢ ((succ a) ≤ b) := by
  -- Paso 1: Tricotomía para σ(a) y b (ax19)
  have h_ax19 := ax (by simp [axioms] : ax19_lt_trichotomy ∈ axioms)
  have h_tric : Γ ⊢ (lt (succ a) b ∨ (succ a =eq b) ∨ lt b (succ a)) := by
    have h := spec (spec h_ax19 (succ a)) b
    -- h : Γ ⊢ substFormula 0 b (substFormula 1 (liftTerm 0 (succ a)) body19)
    -- que computa a  lt(σa,b) ∨ (σa =eq b) ∨ lt(b,σa)
    -- via FOL.substTerm_liftTerm (substTerm c s (liftTerm c t) = t)
    -- y reducción de los índices de de Bruijn numéricos
    simp [substFormula, substTerm, substTerms,
          liftTerm, liftTerms, lt, succ, FOL.substTerm_liftTerm] at h
    exact h
  -- Paso 2: or_elim en modo táctico (el goal provee el tipo implícito B para or_intro_left/right)
  apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h_tric
  · intro h1; exact ROBINSON_PlusPlus.Minimal.Axioms.or_intro_left h1   -- caso lt (succ a) b
  · intro h23
    apply ROBINSON_PlusPlus.Minimal.Axioms.or_elim h23
    · intro h2; exact ROBINSON_PlusPlus.Minimal.Axioms.or_intro_right h2  -- caso succ a = b
    · intro h_blt_sa
      -- Paso 3: caso b < σ(a) — contradicción con h_lt : a < b
      -- Vía ax13: ∃k', a + σ(k') = b   (de h_lt)
      --           ∃k,  b + σ(k)  = σ(a) (de h_blt_sa)
      -- Cadena (THOUGHTS.md):
      --   (a + σ(k')) + σ(k) = σ(a)    [sustituyendo b]
      --   σ((a + σ(k')) + k) = σ(a)    [ax5]
      --   (a + σ(k')) + k = a           [ax3]
      --   σ(k') + k = 0                 [ax7 + ax6 + ax27]
      --   σ(k + k') = 0  ↯ ax2
      exact false_elim (by
        have h_ax13 := ax (by simp [axioms] : ax13_lt_def ∈ axioms)
        -- ax13 para (a, b): a < b ↔ ∃k', a + σ(k') = b
        have h_ax13_ab := by
          have h := spec (spec h_ax13 a) b
          simp [substFormula, substTerm, substTerms,
               lt, add, succ, iff, FOL.substTerm_liftTerm] at h
          exact h
        -- ax13 para (b, succ a): b < σ(a) ↔ ∃k, b + σ(k) = σ(a)
        have h_ax13_bsa := by
          have h := spec (spec h_ax13 b) (succ a)
          simp [substFormula, substTerm, substTerms,
               lt, add, succ, iff, FOL.substTerm_liftTerm] at h
          exact h
        -- Testigos existenciales
        have h_ex_kp := iff_mp h_ax13_ab h_lt
        have h_ex_k  := iff_mp h_ax13_bsa h_blt_sa
        apply ex_elim h_ex_kp; intro kp h_kp
        -- h_kp : Γ ⊢ substFormula 0 kp (add a (succ(.var 0)) =eq b)
        apply ex_elim h_ex_k; intro k h_k
        -- h_k  : Γ ⊢ substFormula 0 k  (add b (succ(.var 0)) =eq succ a)
        -- Cadena aritmética → σ(k + kp) = 0 → contradice ax2
        sorry)

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
