/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.ReprPrf
import ROBINSON_PlusPlus.Meta.HilbertDeduction

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction

set_option linter.unusedSimpArgs false

namespace ROBINSON_PlusPlus.Meta.ChainPrf

/-!
## META — NIVEL D real: lemas de cadena a nivel `Prf` (paso 8)

Port de los lemas de compositividad/monotonía de cadenas (`runFn_concat`,
`chainOk_concat`, `In_mono`, …) al cálculo finitario `Prf`, usando la regla
`Prf.listInd` (inducción de listas) vía el eliminador `prf_list_induction`.
Son los ingredientes de `d2_prf` (concatenación de pruebas + `mp` interno).
-/

/-- **Eliminador de inducción de listas en `Prf`**: de `Prf (Φ[nil])` y
    `Prf (∀h∀t (Φ[t] ⇒ Φ[cons h t]))` sale `Prf (∀L Φ[L])`. -/
theorem prf_list_induction (Φ : Formula)
    (base : Prf (substFormula 0 nil Φ))
    (step : Prf (Formula.forall (Formula.forall (Formula.impl (liftFormula 1 Φ)
              (substFormula 0 (cons (.var 1) (.var 0)) (liftFormula 2 (liftFormula 1 Φ)))))))
    : Prf (Formula.forall Φ) :=
  prf_mp (prf_mp (Prf.listInd Φ) base) step

end ROBINSON_PlusPlus.Meta.ChainPrf

export ROBINSON_PlusPlus.Meta.ChainPrf (prf_list_induction)
