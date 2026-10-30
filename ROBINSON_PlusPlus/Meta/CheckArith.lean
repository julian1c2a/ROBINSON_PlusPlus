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

namespace ROBINSON_PlusPlus.Meta.CheckArith

/-!
## META — NIVEL D (real): verificador object de demostraciones  (Fase 2.4)

`provFormulaC` (la fórmula Σ₁ de demostrabilidad; ✏️ 2026‑10‑14: decía `demFormula`, el
nombre del plan, que no llegó a existir; la de Gödel es `provFormulaC'`, `Meta/ProofChain.lean`)
reposa sobre un verificador
object-level de demostraciones-secuencia **anotadas hacia adelante**: cada línea
lleva su etiqueta de regla (`numeralM 0..17`; ✏️ 2026‑10‑14, ADR‑134: hoy `0..20`, con 18 =
`ax_vpf_ind`, 19 = `ax_vpf_qconf` y 20 = `ax_vpf_listInd`, en `Minimal/Axioms.lean`) y sus
parámetros; el verificador
`validProofFn` recorre la secuencia recomputando la conclusión de cada línea (los
esquemas Q usan `substfc`/`liftfc`, ya hechos) y, para MP/Gen, comprueba la
pertenencia de las premisas vía `In`.

Este archivo define el puente `numeralM_eq` (`numeralM = Godel.numeral`). ✏️ *(2026‑10‑27, ADR‑192, T68)*: definía
también la fórmula Σ₁ `provFormulaC`/`provCodeC` sobre `validProofFn`; el verificador antiguo y sus 22 axiomas
salieron de T, y todo lo de abajo que lo nombra es REGISTRO.

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

-- 🗑️ (2026‑10‑27, ADR‑192, T68) Aquí vivían `provFormulaC` y `provCodeC`, el `Prov` sobre `validProofFn`, sin
-- consumidor desde que la cadena usa `provFormulaC'` (`Meta/ProofChain.lean`): salieron con el verificador antiguo.

end ROBINSON_PlusPlus.Meta.CheckArith

export ROBINSON_PlusPlus.Meta.CheckArith (
  numeralM_eq
)
