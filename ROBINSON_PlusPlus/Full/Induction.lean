/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Minimal.Axioms

import FOL.FOL
import FOL.Tactics
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import FOL.Theorems.Derived
import FOL.Theorems.Quantifiers
import FOL.Deduction

open ROBINSON_PlusPlus.Minimal.Axioms

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Full

/-!
## FULL — INDUCCIÓN GENERAL (object-level, lift-aware)

`Full` añade sobre `Minimal` el **esquema de inducción general** como **axioma
object-level** (`ax_induction`). Las demostraciones de los axiomas algebraicos
de `Minimal` (que aquí pasan a teoremas) se hacen por derivación object-level
—`spec`, `mp`, `gen`, `imp_intro`— usando ese axioma.

**Codificación lift-aware**: `φ(σn)` se codifica como
`substFormula 0 (σ#0) (liftFormula 1 φ)`, que preserva las variables-parámetro
de `φ` (la versión ingenua `substFormula 0 (σ#0) φ` las decrementaba, rompiendo
la inducción multivariable). El lema de composición `substTerm_subst_succ_lift`
+ `step_eq_reduce` reducen el paso a la forma `φ(n) ⇒ φ(σn)` con sustituciones
únicas, manejables como en `Minimal`.
-/

/-! ### Lema de composición de sustitución (De Bruijn, offset 0) -/

mutual
theorem substTerm_subst_succ_lift (m t : Term) :
    substTerm 0 m (substTerm 0 (succ (.var 0)) (liftTerm 1 t)) = substTerm 0 (succ m) t := by
  cases t with
  | var j =>
    by_cases hj : j = 0
    · subst hj; simp [liftTerm, substTerm, substTerms, succ]
    · have h1 : ¬ j < 1 := by omega
      have h2 : ¬ (j + 1 = 0) := by omega
      have h3 : j + 1 > 0 := by omega
      have h4 : j > 0 := by omega
      simp [liftTerm, substTerm, substTerms, succ, hj, h1, h2, h3, h4]
  | func f ts =>
    simp only [liftTerm, substTerm]
    congr 1
    exact substTerms_subst_succ_lift m ts
theorem substTerms_subst_succ_lift (m : Term) (ts : List Term) :
    substTerms 0 m (substTerms 0 (succ (.var 0)) (liftTerms 1 ts)) = substTerms 0 (succ m) ts := by
  cases ts with
  | nil => simp [liftTerms, substTerms]
  | cons t ts' =>
    simp only [liftTerms, substTerms]
    rw [substTerm_subst_succ_lift m t, substTerms_subst_succ_lift m ts']
end

/-- Composición para fórmulas de igualdad (suficiente: las fórmulas de inducción
    algebraica son ecuaciones, sin cuantificadores internos). -/
theorem substFormula_eq_succ_lift (n t u : Term) :
    substFormula 0 n (substFormula 0 (succ (.var 0)) (liftFormula 1 (Formula.eq t u)))
      = substFormula 0 (succ n) (Formula.eq t u) := by
  show Formula.eq (substTerm 0 n (substTerm 0 (succ (.var 0)) (liftTerm 1 t)))
                  (substTerm 0 n (substTerm 0 (succ (.var 0)) (liftTerm 1 u)))
     = Formula.eq (substTerm 0 (succ n) t) (substTerm 0 (succ n) u)
  rw [substTerm_subst_succ_lift, substTerm_subst_succ_lift]

/-- Reduce el cuerpo del paso de inducción (para `φ` ecuación) a `φ(n) ⇒ φ(σn)`. -/
theorem step_eq_reduce (n t u : Term) :
    substFormula 0 n (Formula.impl (Formula.eq t u)
        (substFormula 0 (succ (.var 0)) (liftFormula 1 (Formula.eq t u))))
      = Formula.impl (substFormula 0 n (Formula.eq t u)) (substFormula 0 (succ n) (Formula.eq t u)) := by
  show Formula.impl (substFormula 0 n (Formula.eq t u))
        (substFormula 0 n (substFormula 0 (succ (.var 0)) (liftFormula 1 (Formula.eq t u))))
     = Formula.impl (substFormula 0 n (Formula.eq t u)) (substFormula 0 (succ n) (Formula.eq t u))
  rw [substFormula_eq_succ_lift]

/-! ### Esquema de inducción general (axioma object-level) -/

/-- Fórmula de inducción para `φ` (variable libre `0`), lift-aware:
    `φ(0) ⇒ ((∀n. φ(n) ⇒ φ(σn)) ⇒ ∀n. φ(n))` con `φ(σn) = substFormula 0 (σ#0) (liftFormula 1 φ)`. -/
def inductionFormula (φ : Formula) : Formula :=
  Formula.impl (substFormula 0 zero φ)
    (Formula.impl
      (Formula.forall (Formula.impl φ (substFormula 0 (succ (.var 0)) (liftFormula 1 φ))))
      (Formula.forall φ))

/-- **Esquema de inducción general** como axioma object-level. -/
axiom ax_induction (φ : Formula) : axioms ⊢ inductionFormula φ

/-- Empaquetado object-level (doble `mp` sobre `ax_induction`). No es regla meta. -/
theorem induction_object {φ : Formula}
    (base : axioms ⊢ substFormula 0 zero φ)
    (step : axioms ⊢ Formula.forall
              (Formula.impl φ (substFormula 0 (succ (.var 0)) (liftFormula 1 φ)))) :
    axioms ⊢ Formula.forall φ := by
  have hind := ax_induction φ
  simp only [inductionFormula] at hind
  exact mp (mp hind base) step

/-! ### `zero_add` (sin parámetro) -/

theorem zero_add : axioms ⊢ Formula.forall (add zero (.var 0) =eq (.var 0)) := by
  apply induction_object
  · show axioms ⊢ (add zero zero =eq zero)
    have h := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) zero
    simp [substFormula, substTerm, substTerms, add, zero] at h
    exact h
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro hn
    have hn' : axioms ⊢ (add zero n =eq n) := hn
    show axioms ⊢ (add zero (succ n) =eq succ n)
    have h5 : axioms ⊢ (add zero (succ n) =eq succ (add zero n)) := by
      have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) zero) n
      simp [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at hh
      exact hh
    exact FOL.derive_eq_trans h5 (eq_congr_succ hn')

/-! ### `succ_add` (con parámetro) -/

theorem succ_add (a : Term) :
    axioms ⊢ Formula.forall
      (add (succ (liftTerm 0 a)) (.var 0) =eq succ (add (liftTerm 0 a) (.var 0))) := by
  apply induction_object
  · -- base: add (σa) 0 = σ(add a 0)
    simp only [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm]
    have hA : axioms ⊢ (add (succ a) zero =eq succ a) := by
      have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) (succ a)
      simp [substFormula, substTerm, substTerms, add, zero, succ] at hh
      exact hh
    have hB : axioms ⊢ (add a zero =eq a) := by
      have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) a
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    exact FOL.derive_eq_trans hA (eq_symm (eq_congr_succ hB))
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    have h5sa : axioms ⊢ (add (succ a) (succ n) =eq succ (add (succ a) n)) := by
      have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) (succ a)) n
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    have h5a : axioms ⊢ (add a (succ n) =eq succ (add a n)) := by
      have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) a) n
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    exact FOL.derive_eq_trans (FOL.derive_eq_trans h5sa (eq_congr_succ ih))
      (eq_symm (eq_congr_succ h5a))

/-! ### `add_comm` (= `ax6`) por inducción object-level -/

theorem add_comm_ax (a : Term) :
    axioms ⊢ Formula.forall
      (add (liftTerm 0 a) (.var 0) =eq add (.var 0) (liftTerm 0 a)) := by
  apply induction_object
  · -- base: add a 0 = add 0 a
    simp only [substFormula, substTerm, substTerms, add, zero, FOL.substTerm_liftTerm]
    have hA : axioms ⊢ (add a zero =eq a) := by
      have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) a
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    have hB : axioms ⊢ (add zero a =eq a) := by
      have hh := spec zero_add a
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    exact FOL.derive_eq_trans hA (eq_symm hB)
  · apply gen; intro n
    rw [step_eq_reduce]
    apply Minimal.Axioms.imp_intro; intro ih
    simp only [substFormula, substTerm, substTerms, add, succ, zero, FOL.substTerm_liftTerm] at ih ⊢
    have h5 : axioms ⊢ (add a (succ n) =eq succ (add a n)) := by
      have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) a) n
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    have hsucc : axioms ⊢ (add (succ n) a =eq succ (add n a)) := by
      have hh := spec (succ_add n) a
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    exact FOL.derive_eq_trans (FOL.derive_eq_trans h5 (eq_congr_succ ih)) (eq_symm hsucc)

/-- **`ax6` de `Minimal` es teorema en `Full`**: `⊢ ∀a ∀b, a+b = b+a`. -/
theorem add_comm_thm : axioms ⊢ ax6_add_comm := by
  apply gen; intro a
  exact add_comm_ax a

end ROBINSON_PlusPlus.Full
