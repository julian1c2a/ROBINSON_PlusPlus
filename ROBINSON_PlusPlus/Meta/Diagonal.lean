/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Representability

import FOL.FOL
import FOL.Theorems.Eq
import FOL.Deduction
import FOL.Theorems.Derived
import FOL.Theorems.Impl
import FOL.Theorems.Neg
import ROBINSON_PlusPlus.Meta.Hilbert

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`. Los nombres de esa capa que cite el texto de abajo
> (`tc_zero`, `tc_succ`, `tc_numeral`, `congr_tc2`, `subst_eq_iff`, y los ayudantes `ax`/`spec` sobre `⊢`)
> **ya no existen**: lo que se lea sobre ellos es REGISTRO, no estado.
> Lo que queda en el módulo no depende de `⊢`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.Representability
open ROBINSON_PlusPlus.Meta.Hilbert

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.Diagonal

/-!
## META — NIVEL D (real): lema diagonal  (Fase 4) — cimientos

Para el **lema diagonal** (punto fijo `⊢ G ⇔ φ(⌜G⌝)`) hace falta representar la
diagonalización: substituir el código de una fórmula en sí misma, lo que requiere
el **código del código** `termCode (formCode ψ)`. La función object `tcFn`
(`Minimal/Axioms.lean`) computa `termCode` sobre códigos.

🗑️ **2026‑10‑02 (ADR‑115):** aquí se re-derivaban sus ecuaciones como teoremas `axioms ⊢ …`
(`tc_zero`, `tc_succ`, vía `ax`+`spec`, puentes `numeralM_eq`/`strCodeM_eq`) y se probaba
`tc_numeral` (cómputo sobre numerales) por inducción meta, con la congruencia `congr_tc2`; todo se
retiró con la capa `⊢`. Sus versiones `Prf` son `prf_tc_zero`, `prf_tc_succ`, `prf_tc_numeral` y
`prf_congr_tc2` (`Meta/TcArithPrf.lean`). La cadena `tc_arith` sobre TODO código (`tc_of_cons`,
`tc_chars`/`tc_str`/`tc_term`/`tc_form`) se había retirado antes, con `ax_tc_cons`. **Hoy el módulo
sólo define** `selfApp`, `diagTerm`, `godelPred`, `godelBeta` y `godelC`, y prueba `godel_comp` (una
igualdad de sintaxis, sin cálculo).
-/

-- [REPARACION] Familia SINTACTICA de `tc` RETIRADA con `ax_tc_cons`.
-- Sustituida por la via NUMERAL: `prf_formCode_numeral` (`Meta/CodeNumeralPrf.lean`) y, sobre
-- `Prf`, `prf_diag_arith_num`/`prf_godelCN_fixedpoint` (`Meta/GodelTwoPrf.lean`).

/-! ### Función de diagonalización representada (`selfApp`, `diagTerm`) -/

/-- **Auto-aplicación**: `ψ` con su propio código sustituido en su variable libre 0. -/
def selfApp (ψ : Formula) : Formula := substFormula 0 (formCode ψ) ψ

/-- **Término de diagonalización** (variable libre 0). Usa `tcFn` (código del código) y `substfc`.
    Aplicado al código **numeral** `numeral (codeNat ψ)` produce, en `Prf`,
    `numeral (codeNat (selfAppN ψ))`: es `prf_diag_arith_num` (`Meta/GodelTwoPrf.lean`). (La lectura
    en árbol, `diagTerm[⌜ψ⌝] = ⌜selfApp ψ⌝`, era `diag_arith`: necesitaba `tc_form`, o sea
    `ax_tc_cons`, y se retiró con él.) -/
def diagTerm : Term := substfc (numeral 0) (tcFn (Term.var 0)) (Term.var 0)

-- [REPARACION] Familia SINTACTICA de `tc` RETIRADA con `ax_tc_cons`.
-- Sustituida por la via NUMERAL: `prf_formCode_numeral` (`Meta/CodeNumeralPrf.lean`) y, sobre
-- `Prf`, `prf_diag_arith_num`/`prf_godelCN_fixedpoint` (`Meta/GodelTwoPrf.lean`).

/-! ### Predicado y sentencia de Gödel (`godelPred`, `godelBeta`, `godelC`)

(Esta sección se llamaba «Punto fijo (lema diagonal) y Primer Teorema de Gödel real»: el punto fijo
y Gödel I sobre `godelC` se retiraron con `ax_tc_cons`, y `subst_eq_iff` —Leibniz sobre `⊢`— con
ADR‑115; su versión `Prf` es `prf_subst_eq_iff`, en `Meta/GodelTwoPrf.lean`.)

Para el predicado concreto de Gödel `godelPred = ¬provFormulaC` (una variable
libre, sin variables libres ≥ 1) la composición de sustituciones se reduce con un
único `substTerm_lift_comm` (no hace falta el lema general De Bruijn). -/


/-- Predicado de Gödel `¬Prov(·)` (variable libre 0). -/
def godelPred : Formula := neg provFormulaC

/-- Predicado diagonalizado `β` (variable libre 0). -/
def godelBeta : Formula := substFormula 0 diagTerm godelPred

/-- **Sentencia de Gödel real** `G = β(⌜β⌝)`. -/
noncomputable def godelC : Formula := selfApp godelBeta

/-- Composición de sustituciones para `godelPred` (sin var libre ≥ 1): se reduce
    con `substTerm_lift_comm`. -/
theorem godel_comp (s : Term) :
    substFormula 0 s godelBeta = substFormula 0 (substTerm 0 s diagTerm) godelPred := by
  simp [godelBeta, godelPred, neg, provFormulaC, substFormula, substTerm, substTerms,
    In, validProofFn, nil, zero, FOL.substTerm_liftTerm, FOL.substTerm_lift_comm]

-- [REPARACION] Familia SINTACTICA de `tc` RETIRADA con `ax_tc_cons`.
-- Sustituida por la via NUMERAL: `prf_formCode_numeral` (`Meta/CodeNumeralPrf.lean`) y, sobre
-- `Prf`, `prf_diag_arith_num`/`prf_godelCN_fixedpoint` (`Meta/GodelTwoPrf.lean`).

end ROBINSON_PlusPlus.Meta.Diagonal

export ROBINSON_PlusPlus.Meta.Diagonal (
  selfApp
  diagTerm
  godelPred
  godelBeta
  godelC
)
