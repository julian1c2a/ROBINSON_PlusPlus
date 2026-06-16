/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.StepArith

import FOL.FOL
import FOL.Theorems.Eq

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.CheckArith

/-!
## META — NIVEL D (real): verificador object de demostraciones  (Fase 2.4)

`demFormula` (la fórmula Σ₁ de demostrabilidad) reposa sobre un verificador
object-level de demostraciones-secuencia **anotadas hacia adelante**: cada línea
lleva su etiqueta de regla (`numeralM 0..17`) y sus parámetros; el verificador
`validProofFn` recorre la secuencia recomputando la conclusión de cada línea (los
esquemas Q usan `substfc`/`liftfc`, ya hechos) y, para MP/Gen, comprueba la
pertenencia de las premisas vía `In`.

Este archivo arranca con los **extractores** `carc`/`cdrc` (cabeza/cola de
`cons`) computados, y el puente `numeralM = Godel.numeral`. El ensamblaje de
`validProofFn` + `demFormula` sigue (las ecuaciones van en `Minimal.axioms`).
-/

/-- `numeralM` (Minimal) coincide con `Godel.numeral` (misma definición). -/
theorem numeralM_eq (n : Nat) : numeralM n = ROBINSON_PlusPlus.Meta.Godel.numeral n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [numeralM, ROBINSON_PlusPlus.Meta.Godel.numeral, ih]

/-- Cómputo de `carc (cons h t) = h`. -/
theorem carc_cons (h t : Term) : axioms ⊢ (carc (cons h t) =eq h) := by
  have hh := spec (spec (ax (show ax_carc ∈ axioms by simp [axioms])) h) t
  simp [ax_carc, substFormula, substTerm, substTerms, carc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

/-- Cómputo de `cdrc (cons h t) = t`. -/
theorem cdrc_cons (h t : Term) : axioms ⊢ (cdrc (cons h t) =eq t) := by
  have hh := spec (spec (ax (show ax_cdrc ∈ axioms by simp [axioms])) h) t
  simp [ax_cdrc, substFormula, substTerm, substTerms, cdrc, cons, nil, zero, succ,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

end ROBINSON_PlusPlus.Meta.CheckArith

export ROBINSON_PlusPlus.Meta.CheckArith (
  numeralM_eq
  carc_cons
  cdrc_cons
)
