/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL
import FOL.Theorems.Eq
import ROBINSON_PlusPlus.Meta.SubstArith

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`: los extractores (`carc_cons`, `cdrc_cons`) y los pasos de
> `validProofFn` (`vpf_nil`, `vpf_p1` … `vpf_listInd`) **ya no existen**; lo que se lea sobre ellos es
> REGISTRO, no estado. Lo que queda en el módulo no depende de `⊢`.
-/

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

Este archivo define la fórmula Σ₁ concreta `provFormulaC`/`provCodeC` sobre `validProofFn`
(cuyas ecuaciones son entradas de `Minimal.axioms`) y el puente `numeralM_eq`
(`numeralM = Godel.numeral`).

🗑️ **2026‑10‑02 (ADR‑115) — registro.** El módulo demostraba además, sobre `⊢`, el cómputo de los
**extractores** `carc`/`cdrc` (cabeza/cola de `cons`) y los pasos de `validProofFn`, re‑derivados
de `Minimal.axioms`. Esos lemas quedaron retirados con la capa `⊢`; los símbolos `carc`, `cdrc` y
`validProofFn` siguen en `Minimal/Axioms.lean`. En `Prf` el cómputo de los extractores es
`prf_carc_cons` (`Meta/ReprPrf.lean`) y `prf_cdrc_cons` (`Meta/CodeWitnessPrf.lean`); los pasos de
`validProofFn` no tienen versión `Prf`: la cadena sobre `Prf` usa el predicado estructural
`provCodeC'` (`chainOk`/`runFn`, `Meta/ProofChain.lean`).
-/

/-- `numeralM` (Minimal) coincide con `Godel.numeral` (misma definición). -/
theorem numeralM_eq (n : Nat) : numeralM n = ROBINSON_PlusPlus.Meta.Godel.numeral n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [numeralM, ROBINSON_PlusPlus.Meta.Godel.numeral, ih]

-- (Aquí vivían, sobre `⊢`, `carc_cons`/`cdrc_cons` y los pasos de `validProofFn`; retirados con
-- ADR‑115.)

/-! ### Fórmula de demostrabilidad object Σ₁ -/

/-- **Predicado de demostrabilidad object** (Σ₁): `∃ p, In x (validProofFn nil p)`
    — "existe una demostración-secuencia `p` cuyas conclusiones contienen `x`".
    `x` ocupa la variable libre 0 (convención de `substFormula 0 ⌜φ⌝ ·`). Versión
    **concreta** del `provFormula` que postulaba `Meta/Provability.lean` (capa legacy, retirada
    en F7a, 2026‑07‑09). -/
def provFormulaC : Formula := Formula.ex (In (Term.var 1) (validProofFn nil (Term.var 0)))

/-- `Prov(⌜φ⌝)` concreto. -/
noncomputable def provCodeC (φ : Formula) : Formula := substFormula 0 (formCode φ) provFormulaC

end ROBINSON_PlusPlus.Meta.CheckArith

export ROBINSON_PlusPlus.Meta.CheckArith (
  provFormulaC
  provCodeC
  numeralM_eq
)
