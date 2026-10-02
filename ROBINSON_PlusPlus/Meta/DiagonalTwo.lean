/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Representability2
import ROBINSON_PlusPlus.Meta.Diagonal

import FOL.FOL
import FOL.Theorems.Eq

/-!
> 🗑️ **2026‑10‑02 · ADR‑115 — leer antes que el resto.** La capa `⊢` se retiró de RPP, y con ella todo lo
> que este módulo tenía sobre `⊢`. Los nombres de esa capa que cite el texto de abajo
> (`subst_eq_iff`, `goedel_first_unprovable_real'`, `goedel_first_unrefutable_real'`, `Reflects`,
> `godelCN_fixedpoint`, `goedel_first_numeral`, `repr_pos'`, `reflects_of_omega`, `OmegaConsistent`,
> `NegVerifier`, `negVerifier_proved`, `formCode_ne`) **ya no existen**: lo que se lea sobre ellos es REGISTRO, no estado.
> Lo que queda en el módulo no depende de `⊢`.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.SubstArith
open ROBINSON_PlusPlus.Meta.CheckArith
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.Representability2
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Diagonal

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.DiagonalTwo

/-!
## META — NIVEL D real: punto fijo para `provCodeC'` (hacia Gödel II)

Instancia la maquinaria diagonal **genérica** de `Meta/Diagonal.lean` (`diagTerm`, `selfApp`)
con el predicado de demostrabilidad **estructural** `provFormulaC'` (verificador
`runFn`/`chainOk`), produciendo la sentencia de Gödel `godelC'`. (`diag_arith` se retiró con
`ax_tc_cons`; `subst_eq_iff`, Leibniz sobre `⊢`, con ADR‑115: su versión `Prf` es
`prf_subst_eq_iff`, en `Meta/GodelTwoPrf.lean`.)

> ⚠️ **ACTUALIZADO 2026‑08‑19 (reparación de la inconsistencia).** `godelC'_fixedpoint` **se ha
> RETIRADO**: dependía de `diag_arith` → `tc_form`, o sea de `ax_tc_cons`, la ecuación que hacía
> INCONSISTENTE la teoría. El punto fijo pasó entonces a `Meta/DiagonalNumeral.lean`, sobre la
> sentencia **numeral** `godelCN` (`godelCN_fixedpoint`, sobre `⊢`).
>
> 🗑️ **2026‑10‑02 (ADR‑115):** `godelCN_fixedpoint`, `goedel_first_numeral` y los dos teoremas
> **modulares** de este módulo (`goedel_first_unprovable_real'` / `_unrefutable_real'`, que tomaban
> el punto fijo como hipótesis) se retiraron con la capa `⊢`. El punto fijo sobre `Prf` es
> `prf_godelCN_fixedpoint` (`Meta/GodelTwoPrf.lean`), y Gödel I es `goedel_first_prf` (⛔ vacuo por
> `[AnclaEq]`, F1, ADR‑114).
>
> ⟹ **`godelC'` es hoy una definición sin punto fijo.** Lo que se usa es `godelCN`. Aquí sólo
> quedan las definiciones (`godelPred'`, `godelBeta'`, `godelC'`) y `godel_comp'`, que consume
> `prf_godelCN_fixedpoint_N` (`Meta/GodelTwoPrf.lean`).

El único punto delicado es la composición de sustituciones (`godel_comp'`): como
`godelPred'` no tiene variables libres ≥ 1, se reduce con un único
`substTerm_lift_comm` (igual que en `Meta/Diagonal.lean`).
-/

/-- Predicado de Gödel estructural `¬Prov'(·)` (variable libre 0). -/
def godelPred' : Formula := neg provFormulaC'

/-- Predicado diagonalizado `β'` (variable libre 0). -/
def godelBeta' : Formula := substFormula 0 diagTerm godelPred'

/-- **Sentencia de Gödel estructural** `G' = β'(⌜β'⌝)`. -/
noncomputable def godelC' : Formula := selfApp godelBeta'

/-- Composición de sustituciones para `godelPred'` (sin var libre ≥ 1): se reduce
    con `substTerm_lift_comm`. -/
theorem godel_comp' (s : Term) :
    substFormula 0 s godelBeta' = substFormula 0 (substTerm 0 s diagTerm) godelPred' := by
  simp [godelBeta', godelPred', neg, provFormulaC', substFormula, substTerm, substTerms,
    land, chainOk, In, runFn, nil, zero, FOL.substTerm_liftTerm, FOL.substTerm_lift_comm]

-- [REPARACION] `godelC'_fixedpoint` y sus dos direcciones RETIRADOS: usaban `diag_arith`,
-- o sea `tc_form`. Los sustituyó `godelCN_fixedpoint` (`Meta/DiagonalNumeral.lean`, sobre `⊢`),
-- retirado a su vez con ADR‑115; hoy es `prf_godelCN_fixedpoint` (`Meta/GodelTwoPrf.lean`).

/-! (Aquí vivía `goedel_first_unprovable_real'`, Gödel I modular para `provCodeC'`, sobre `⊢`;
retirado con ADR‑115.) -/

-- [REPARACION] `goedel_first_real'` RETIRADO (descargaba el punto fijo roto).
-- Lo sustituyó `goedel_first_numeral` (`Meta/DiagonalNumeral.lean`), retirado a su vez con
-- ADR‑115; hoy Gödel I es `goedel_first_prf` (`Meta/GodelTwoPrf.lean`).

/-! ## La otra mitad de Gödel I (`⊬¬G`) — con la REFLEXIÓN como hipótesis EXPLÍCITA (registro)

🗑️ **2026‑10‑02 (ADR‑115) — registro.** Aquí vivían `Reflects` y `goedel_first_unrefutable_real'`,
sobre `⊢`; se retiraron con esa capa. **La mitad `⊬¬G` no tiene hoy formulación sobre `Prf`**: el
camino elegido es **Rosser** (ADR‑115 §4 y §7). Queda la historia, y el argumento de por qué la
reflexión no puede derivarse dentro de la teoría.

**Historia (leer antes de tocar esto).** Esta mitad se «cerró» el 2026‑06‑13 en la capa LEGACY
(`Meta/Incompleteness.lean`) apoyándose en `provFormula_repr`, **postulado como bicondicional**
`(axioms ⊢ Prov⌜φ⌝) ↔ (axioms ⊢ φ)`. Su dirección `.mp` es la **representabilidad NEGATIVA**
(reflexión), y **NO se sigue de la consistencia simple** — pero el teorema se enunciaba bajo
`Consistent`, es decir **afirmaba más de lo que Gödel permite** (por eso existe **Rosser**: para
obtener ambas mitades desde consistencia simple hay que **cambiar de sentencia**). Era un **postulado
falso en general**. **F7a lo retiró, y con razón.**

**Por qué la reflexión NO puede derivarse dentro de la teoría.** Se necesitaría
`axioms ⊢ ¬ provCodeC' φ` para `φ` indemostrable. Tomando `φ = ⊥` (indemostrable si la teoría es
consistente), eso es **literalmente `Con(T)`** — y por **Gödel II** la teoría no lo demuestra. Para
`φ = G` tampoco: por el punto fijo, `⊢ ¬provCodeC' G` ⟺ `⊢ G`, y `⊬ G` (Gödel I). La vía «la teoría
refuta la demostrabilidad» está **cerrada por Gödel**, no por falta de trabajo.

**Formulación honesta (registro).** La reflexión era una hipótesis **META** (como la ω‑consistencia
clásica), y se dejaba **explícita y a la vista** (`Reflects`, retirado con ADR‑115). Descargarla exigía
ω‑consistencia + **Δ₀‑completitud NEGATIVA del verificador en testigos concretos** (el espejo de
`repr_pos'`, retirado; su cimiento sobre `⊢`, `formCode_ne` de `Meta/CodeDistinct.lean`, también).
Sobre `⊢` se llegó a la reducción —`reflects_of_omega`: `OmegaConsistent` + `NegVerifier` ⇒
`Reflects`—, retirada con ADR‑115. ⛔ Y no descargaba nada: `NegVerifier` no estaba demostrado (la
prueba de `negVerifier_proved` llevaba meta‑reglas refutadas) y `OmegaConsistent` era refutable por
su definición (L1‑4, ADR‑114; ADR‑115 §4). -/


-- [REPARACION] `goedel_first_undecidable_real'` RETIRADO (usaba goedel_first_real').

end ROBINSON_PlusPlus.Meta.DiagonalTwo

export ROBINSON_PlusPlus.Meta.DiagonalTwo (
  godelPred'
  godelBeta'
  godelC'
  godel_comp'
)
