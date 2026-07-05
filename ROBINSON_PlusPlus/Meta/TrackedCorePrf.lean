/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Sigma1TrackedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ProofChain
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1CorePrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.TrackedCorePrf

/-!
## META — NIVEL D real (Opción A DE RAÍZ): infraestructura de clausura genérica

Hacia **D1ₜ** (`repr_pos'_prfₜ`) y los combinadores rastreados. Primer ladrillo: la
**clausura de `provFromCode c` bajo `liftFormula`** para un **código cerrado arbitrario** `c`
(hoy solo existía para `provCodeC'` = `provFromCode ∘ formCode`, vía `liftFormula_provCodeC'`,
y para `exc Ac`, vía `liftFormula_provFromCode_exc`). La versión genérica la necesitan tanto
D1ₜ como el `∃`/MP a nivel de código con códigos `tcFn` (no `formCode`).

### Diagnóstico del cuello de botella (sesión 2026‑07‑05b)

`hI_tracked` abstracto necesita `provFromCode(inFormCodeFn (tcFn ⌜φ⌝) (tcFn L))` con `L`
abstracta. TODA vía por D1 (`repr_pos'`) emite el código vía `termCode` (meta); transportar el
2º argumento `termCode L → tcFn L` está **stuck** para `L` abstracta (el 1º, `⌜φ⌝` concreto, sí
transporta vía `prf_tc_form`). ⇒ **No hay atajo**: hay que **re‑derivar la representabilidad
emitiendo códigos `tcFn` nativamente** (reconstruir `proofCode'`/`runFn_track`/`chainOk_track`
de `Representability2Prf` en la capa `tcFn`). Eso es **D1ₜ**, el port grande. Este módulo abre
esa fase con la clausura genérica; ver `GODEL-D3-TRACKED-DESIGN.md` §4.2/§5 (Opción A).
-/

/-- **Clausura genérica de `provFromCode`**: para un código **cerrado** `c`
    (`∀ lvl, liftTerm lvl c = c`), `provFromCode c` es invariante bajo `liftFormula`.
    Generaliza `liftFormula_provCodeC'` (c = `formCode φ`) y `liftFormula_provFromCode_exc`
    (c = `exc Ac`). -/
theorem liftFormula_provFromCode (k : Nat) (c : Term) (hc : ∀ lvl, liftTerm lvl c = c) :
    liftFormula k (provFromCode c) = provFromCode c := by
  simp only [provFromCode, provFormulaC', substFormula, substTerm, substTerms, liftFormula,
    liftTerm, liftTerms, land, chainOk, In, runFn, nil, zero, Nat.reduceAdd, Nat.reduceLT,
    Nat.reduceEqDiff, Nat.reduceGT, Nat.reduceSub, reduceIte, Nat.zero_lt_succ, if_true,
    FOL.substTerm_liftTerm, FOL.substTerm_liftLift, hc]

end ROBINSON_PlusPlus.Meta.TrackedCorePrf

export ROBINSON_PlusPlus.Meta.TrackedCorePrf (
  liftFormula_provFromCode
)
