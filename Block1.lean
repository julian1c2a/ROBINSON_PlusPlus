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
open FOL.Formula
open FOL.Derives

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
theorem teo_1_1 : Γ ⊢ add one zero =eq one := by
  have h_ax4 : Γ ⊢ ax4_add_zero := ax (by simp [axioms, ax4_add_zero])
  exact spec h_ax4 (t := one)

-- Teo 1.2: 0 + 1 = 1
-- Prueba: 0 + 1 = 1 + 0 (Ax 6) y 1 + 0 = 1 (Teo 1.1).
theorem teo_1_2 : Γ ⊢ add zero one =eq one := by
  have h_ax6 : Γ ⊢ ax6_add_comm := ax (by simp [axioms, ax6_add_comm])
  let h_spec_m := spec h_ax6 (t := one)
  let h_spec_n := spec h_spec_m (t := zero)
  exact eq_trans h_spec_n teo_1_1

-- Teo 1.3: 1 + 1 = 2
-- Prueba: 1 + 1 = 1 + σ(0) = σ(1 + 0) = σ(1) = 2
theorem teo_1_3 : Γ ⊢ add one one =eq two := by
  -- 1. ⊢ 1 + 1 = 1 + σ(0)
  -- This is definitional since one := succ zero.
  have h1 : Γ ⊢ add one one =eq add one (succ zero) := eq_refl

  -- 2. ⊢ 1 + σ(0) = σ(1 + 0)
  -- From Ax 5 (∀n,∀m, n + σ(m) = σ(n+m)) with n:=1, m:=0
  have h_ax5 : Γ ⊢ ax5_add_succ := ax (by simp [axioms, ax5_add_succ])
  let h_spec_m := spec h_ax5 (t := zero)
  let h_spec_n := spec h_spec_m (t := one)
  have h2 := h_spec_n

  -- 3. ⊢ σ(1 + 0) = σ(1)
  -- From Teo 1.1 (1 + 0 = 1) by congruence.
  have h3 : Γ ⊢ succ (add one zero) =eq succ one := eq_congr_succ teo_1_1

  -- 4. ⊢ σ(1) = 2
  -- This is definitional since two := succ one.
  have h4 : Γ ⊢ succ one =eq two := eq_refl

  -- Chain them with transitivity
  exact eq_trans h1 (eq_trans h2 (eq_trans h3 h4))

-- Teo 1.4: 2 + 1 = 3
-- Prueba: 2 + 1 = 2 + σ(0) = σ(2 + 0) = σ(2) = 3
theorem teo_1_4 : Γ ⊢ add two one =eq three := by
  -- 1. ⊢ 2 + 1 = 2 + σ(0)
  have h1 : Γ ⊢ add two one =eq add two (succ zero) := eq_refl

  -- 2. ⊢ 2 + σ(0) = σ(2 + 0)
  -- From Ax 5 with n:=2, m:=0
  have h_ax5 : Γ ⊢ ax5_add_succ := ax (by simp [axioms, ax5_add_succ])
  let h_spec_m := spec h_ax5 (t := zero)
  let h_spec_n := spec h_spec_m (t := two)
  have h2 := h_spec_n

  -- 3. ⊢ σ(2 + 0) = σ(2)
  -- From Ax 4 (∀n, n+0=n) with n:=2, by congruence.
  have h_ax4 : Γ ⊢ ax4_add_zero := ax (by simp [axioms, ax4_add_zero])
  have h_spec_n_ax4 : Γ ⊢ add two zero =eq two := spec h_ax4 (t := two)
  have h3 : Γ ⊢ succ (add two zero) =eq succ two := eq_congr_succ h_spec_n_ax4

  -- 4. ⊢ σ(2) = 3
  -- Definitional since three := succ two.
  have h4 : Γ ⊢ succ two =eq three := eq_refl

  -- Chain them
  exact eq_trans h1 (eq_trans h2 (eq_trans h3 h4))

-- Teo 1.5: 1 + 2 = 3
-- Prueba: 1 + 2 = 2 + 1 (Ax 6) y 2 + 1 = 3 (Teo 1.4).
theorem teo_1_5 : Γ ⊢ add one two =eq three := by
  -- 1. ⊢ 1 + 2 = 2 + 1
  -- From Ax 6 (∀n,∀m, n+m=m+n) with n:=1, m:=2
  have h_ax6 : Γ ⊢ ax6_add_comm := ax (by simp [axioms, ax6_add_comm])
  let h_spec_m := spec h_ax6 (t := two)
  let h_spec_n := spec h_spec_m (t := one)
  have h1 := h_spec_n

  -- 2. ⊢ 2 + 1 = 3
  have h2 := teo_1_4

  -- Chain them with transitivity
  exact eq_trans h1 h2

end ROBINSON_PlusPlus.Minimal.Theorems.Block1
