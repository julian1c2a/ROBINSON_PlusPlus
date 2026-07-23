/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.NatMulPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.NatOrderPrf
open ROBINSON_PlusPlus.Meta.NatMulPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.CantorMonoPrf

/-!
## META — NIVEL D real: MONOTONÍA DE CANTOR (entregable **i‑c** de la ruta 1a)

**Objetivo:** `h < cons h t` y `t < cons h t` en `Prf`, es decir **sub‑código < código**. Con eso
la inducción fuerte sobre códigos (ii) es derivable de `ax_induction`, y con ella
`pcc_eval_substfc` (iii) y los 7 tags de `lineWF` que faltan.

⚠️ **`cons h t` NO es defeq a `pair h (σt)`** (verificado): `cons` es `.func "::"` opaco y la
conexión con la aritmética es el **axioma objeto** `ax_L0_cons_def`. Todo el cálculo de esta
sección va por tanto a nivel `Prf`, no por `rfl`.

Cadena de definiciones (`Minimal/Axioms.lean`):
* `cons h t = pair h (σt)`  — `ax_L0_cons_def`
* `pair x y = cantor_func x y = div2 (cantor_poly x y)` — definicional
* `cantor_poly x y = (x + y)·σ(x + y) + 2·y` — definicional
-/

/-! ### Paso 1 — el puente `cons ↔ pair` (el único que no es definicional) -/

/-- **`cons h t = pair h (σt)`** — instancia de `ax_L0_cons_def`. Es el puente entre el
    constructor de listas (opaco) y la aritmética de Cantor. -/
theorem prf_cons_def (h t : Term) : Prf (cons h t =eq pair h (succ t)) := by
  have hh := prf_spec (prf_spec (prf_ax (show ax_L0_cons_def ∈ axioms by simp [axioms])) h) t
  simp [ax_L0_cons_def, substFormula, substTerm, substTerms, cons, pair, cantor_func,
    cantor_poly, div2, add, mul, succ, two, one, zero,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift] at hh
  exact hh

end ROBINSON_PlusPlus.Meta.CantorMonoPrf

export ROBINSON_PlusPlus.Meta.CantorMonoPrf (
  prf_cons_def
)
