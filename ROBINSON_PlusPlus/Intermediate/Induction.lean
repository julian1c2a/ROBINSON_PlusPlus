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

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Intermediate

/-!
## INTERMEDIATE — PROTOTIPO DE INDUCCIÓN

Valida la viabilidad del esquema de inducción en este framework FOL antes de
comprometerse con la estructura completa de `Intermediate/` (inducción finita
sobre Φ) o `Full/` (inducción general).

**Esquema de inducción** como meta-axioma `peano_induction` (forma híbrida:
hipótesis de paso meta-nivel, conclusión object-level — análoga a `gen`,
`ex_elim`, `or_elim`).

**Pilar**: derivar `add_comm` (= `ax6` de `Minimal`, postulado allí) como
**teorema** vía inducción, usando sólo `ax4`/`ax5` (recursión de `+`).
Esto demuestra que la inducción añade poder real: lo que `Minimal` postula,
`Intermediate`/`Full` lo prueban.
-/

def Γ := axioms

/-- **Esquema de inducción de Peano** (meta-axioma). Para toda fórmula `φ` con
    variable libre `0`: de `φ(0)` y de `∀n (⊢ φ(n) → ⊢ φ(σn))` se concluye
    `⊢ ∀n φ(n)`. Forma híbrida (paso meta, conclusión object) como `gen`.

    Esto es lo único que `Intermediate/`/`Full/` añaden sobre `Minimal/`; el
    resto del trabajo es derivar los axiomas algebraicos como teoremas. -/
axiom peano_induction (φ : Formula)
    (base : axioms ⊢ substFormula 0 zero φ)
    (step : ∀ n : Term, axioms ⊢ substFormula 0 n φ → axioms ⊢ substFormula 0 (succ n) φ) :
    axioms ⊢ Formula.forall φ

/-!
### Lema 1 — `zero_add` por inducción (sin `ax6`)

A diferencia de `teo_2_2` (que usa `ax6`), aquí se prueba `∀n, 0+n = n` por
inducción usando sólo `ax4`/`ax5`. Es el primer escalón hacia `add_comm`.
-/

theorem zero_add_ind : axioms ⊢ Formula.forall (add zero (.var 0) =eq (.var 0)) := by
  apply peano_induction
  · -- base: 0 + 0 = 0  (ax4 instanciado en 0)
    show axioms ⊢ (add zero zero =eq zero)
    have h := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) zero
    simp [substFormula, substTerm, substTerms, add, zero] at h
    exact h
  · -- paso: (0 + n = n) → (0 + σn = σn)
    intro n ih
    have ih' : axioms ⊢ (add zero n =eq n) := ih
    show axioms ⊢ (add zero (succ n) =eq succ n)
    have h5 : axioms ⊢ (add zero (succ n) =eq succ (add zero n)) := by
      have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) zero) n
      simp [substFormula, substTerm, substTerms, add, succ, zero,
            FOL.substTerm_liftTerm] at hh
      exact hh
    exact FOL.derive_eq_trans h5 (eq_congr_succ ih')

/-!
### Lema 2 — `succ_add` por inducción (multivariable, sin `ax6`)

`∀ a n, σa + n = σ(a + n)`, por inducción sobre `n` con `a` parámetro (Lean).
El parámetro se introduce como `liftTerm 0 a` para no ser capturado por la
variable de inducción; `FOL.substTerm_liftTerm` lo recupera al sustituir.
-/

theorem succ_add_ind (a : Term) :
    axioms ⊢ Formula.forall
      (add (succ (liftTerm 0 a)) (.var 0) =eq succ (add (liftTerm 0 a) (.var 0))) := by
  apply peano_induction
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
  · intro n ih
    simp only [substFormula, substTerm, substTerms, add, succ, zero,
               FOL.substTerm_liftTerm] at ih ⊢
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

/-!
### Teorema pilar — `add_comm` por inducción (= `ax6` de Minimal, postulado allí)

`∀ a n, a + n = n + a`, por inducción sobre `n`, usando `zero_add_ind` +
`succ_add_ind` + `ax4`/`ax5`. **No usa `ax6`.** Demuestra que la inducción
convierte en teorema lo que `Minimal` postula.
-/

theorem add_comm_ind (a : Term) :
    axioms ⊢ Formula.forall
      (add (liftTerm 0 a) (.var 0) =eq add (.var 0) (liftTerm 0 a)) := by
  apply peano_induction
  · -- base: add a 0 = add 0 a   (ax4 + zero_add_ind)
    simp only [substFormula, substTerm, substTerms, add, zero, FOL.substTerm_liftTerm]
    have hA : axioms ⊢ (add a zero =eq a) := by
      have hh := spec (ax (by simp [axioms] : ax4_add_zero ∈ axioms)) a
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    have hB : axioms ⊢ (add zero a =eq a) := by
      have hh := spec zero_add_ind a
      simp [substFormula, substTerm, substTerms, add, zero] at hh
      exact hh
    exact FOL.derive_eq_trans hA (eq_symm hB)
  · intro n ih
    simp only [substFormula, substTerm, substTerms, add, succ, zero,
               FOL.substTerm_liftTerm] at ih ⊢
    have h5 : axioms ⊢ (add a (succ n) =eq succ (add a n)) := by
      have hh := spec (spec (ax (by simp [axioms] : ax5_add_succ ∈ axioms)) a) n
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    have hsucc : axioms ⊢ (add (succ n) a =eq succ (add n a)) := by
      have hh := spec (succ_add_ind n) a
      simp [substFormula, substTerm, substTerms, add, succ, FOL.substTerm_liftTerm] at hh
      exact hh
    exact FOL.derive_eq_trans (FOL.derive_eq_trans h5 (eq_congr_succ ih)) (eq_symm hsucc)

/-- **`ax6` de `Minimal` es un teorema en `Intermediate`**: `⊢ ∀a ∀b, a+b = b+a`,
    empaquetando `add_comm_ind` sobre el cuantificador externo vía `gen`. Primer
    eslabón del embedding `Minimal ⊂ Intermediate`. -/
theorem add_comm_thm : axioms ⊢ ax6_add_comm := by
  apply gen
  intro a
  exact add_comm_ind a

end ROBINSON_PlusPlus.Intermediate
