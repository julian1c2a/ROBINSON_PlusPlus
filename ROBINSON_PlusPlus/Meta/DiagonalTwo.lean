/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Representability2
import ROBINSON_PlusPlus.Meta.Diagonal

import FOL.FOL
import FOL.Theorems.Eq

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

Instancia la maquinaria diagonal **genérica** de `Meta/Diagonal.lean` (`diagTerm`,
`diag_arith`, `selfApp`, `subst_eq_iff`) con el predicado de demostrabilidad
**estructural** `provFormulaC'` (verificador `runFn`/`chainOk`), produciendo la
sentencia de Gödel `godelC'` y su **punto fijo real**:

> `godelC'_fixedpoint : ⊢ godelC' ⇔ ¬ provCodeC' godelC'`

Suministra la hipótesis `fp_bwd` de `goedel_second'` (`Meta/GodelTwo.lean`). El
único punto delicado es la composición de sustituciones (`godel_comp'`): como
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
-- o sea `tc_form`. Sustituidos por `Meta/DiagonalNumeral.godelCN_fixedpoint`.

/-! ### Primer Teorema de Gödel REAL para el predicado estructural `provCodeC'` -/

/-- **Gödel I real (indemostrabilidad), modular**, para `provCodeC'`: si la teoría
    verificadora es consistente y `G ⇔ ¬Prov'(⌜G⌝)`, entonces `G` **no** es
    demostrable en el cálculo finitario `Prf`. Usa **D1 honesto** `repr_pos'`. -/
theorem goedel_first_unprovable_real' {G : Formula}
    (hcon : ConsistentOmega)
    (hfp : axioms ⊢ (G ⇔ neg (provCodeC' G))) :
    ¬ Prf G := by
  intro hG
  have hProv : axioms ⊢ provCodeC' G := repr_pos' hG
  have hGder : axioms ⊢ G := prf_to_derives hG
  have fp_fwd : axioms ⊢ (G ⇒ neg (provCodeC' G)) := Minimal.Axioms.and_elim_left hfp
  have hNotProv : axioms ⊢ neg (provCodeC' G) := mp fp_fwd hGder
  exact hcon (mp hNotProv hProv)

-- [REPARACION] `goedel_first_real'` RETIRADO (descargaba el punto fijo roto).
-- Sustituido por `Meta/DiagonalNumeral.goedel_first_numeral`.

/-! ## La otra mitad de Gödel I (`⊬¬G`) — con la REFLEXIÓN como hipótesis EXPLÍCITA

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

**Formulación honesta.** La reflexión es una hipótesis **META** (como la ω‑consistencia clásica), y se
deja **explícita y a la vista** — igual que `goedel_second'` hace con sus hipótesis. Descargarla exige
ω‑consistencia + **Δ₀‑completitud NEGATIVA del verificador en testigos concretos** (el espejo de
`repr_pos'`; cimiento en `Meta/CodeDistinct.lean`). -/

/-- **Reflexión** (hipótesis META): si la teoría demuestra que `G` es demostrable, entonces `G`
    **realmente** lo es. Es la representabilidad **negativa**. **NO se sigue de la consistencia** (para
    `φ = ⊥` sería `Con(T)`, indemostrable por Gödel II): es la hipótesis honesta que el postulado
    legacy `provFormula_repr` escondía. -/
abbrev Reflects (G : Formula) : Prop := (axioms ⊢ provCodeC' G) → Prf G

/-- **`⊬ ¬G` (irrefutabilidad de `G`) — REAL, sin ningún postulado gödeliano**, con la reflexión como
    hipótesis explícita. Argumento (el mismo que el legacy, pero con la dependencia a la vista):
    de `⊢¬G` y el punto fijo `¬Prov'(⌜G⌝) ⇒ G` sale `⊢ ¬¬Prov'(⌜G⌝)`; por `dne` (clásica),
    `⊢ Prov'(⌜G⌝)`; por **reflexión**, `Prf G` — que contradice Gödel I (`goedel_first_unprovable_real'`). -/
theorem goedel_first_unrefutable_real' {G : Formula}
    (hcon : ConsistentOmega)
    (hfp : axioms ⊢ (G ⇔ neg (provCodeC' G)))
    (hrefl : Reflects G) :
    ¬ Prf (neg G) := by
  intro hNotG
  have hNotGder : axioms ⊢ neg G := prf_to_derives hNotG
  have fp_bwd : axioms ⊢ (neg (provCodeC' G) ⇒ G) := FOL.MetaRules.and_elim_right hfp
  have hnn : axioms ⊢ neg (neg (provCodeC' G)) :=
    imp_intro (fun hnp => mp hNotGder (mp fp_bwd hnp))
  have hProv : axioms ⊢ provCodeC' G := FOL.MetaRules.dne hnn
  exact goedel_first_unprovable_real' hcon hfp (hrefl hProv)

-- [REPARACION] `goedel_first_undecidable_real'` RETIRADO (usaba goedel_first_real').

end ROBINSON_PlusPlus.Meta.DiagonalTwo

export ROBINSON_PlusPlus.Meta.DiagonalTwo (
  godelPred' godelBeta' godelC' godel_comp' goedel_first_unprovable_real' Reflects goedel_first_unrefutable_real'
)
