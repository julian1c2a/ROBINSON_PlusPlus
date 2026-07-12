/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.EvalListPrf
import ROBINSON_PlusPlus.Meta.RunFnBoundedPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.TcArithPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.MpCodePrf
open ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
open ROBINSON_PlusPlus.Meta.EvalArithPrf
open ROBINSON_PlusPlus.Meta.EvalListPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.EvalRunFnPrf

/-!
## META — NIVEL D real (§34, arranque): evaluación provable de `runFn`

`hI_dot` (la reflexión punteada del átomo `In ⌜φ⌝ (runFn nil #0)`) necesita puentear el término
**simbólico** `runFn(nil, ṗ)` que aparece en el código dotado (`inDot`) con el **valor**
`(runFn nil p)˙`. Ese puente es la **evaluación provable de `runFn`**:

```text
⊢ Prov( ⌜ runFn(nil, ṗ)  =  (runFn nil p)˙ ⌝ )        para p ARBITRARIO
```

Estructuralmente `runFn nil` es un **map de `carc`** (`prf_runFn_nil_cons`, `RunFnBoundedPrf`):
`runFn nil (cons h t) =eq cons (carc h) (runFn nil t)`, **sin acumulador**. Así que la evaluación es
una inducción de listas (receta §28), con la base aquí resuelta.

**Este módulo entrega la BASE** (`p = nil`). El paso inductivo requiere codificar `ax_runFn_cons`
(que arrastra `concat` y `carc`), y queda como siguiente ladrillo.
-/

/-- Constructor de código del término simbólico `runFn x y`: `⟨1, ⌜runFn⌝, [x, y]⟩`. -/
def runFnT (x y : Term) : Term := funcc (strCode "runFn") (cons x (cons y nil))

/-- Código de la evaluación de `runFn nil p`: *el término simbólico `runFn(ṅil, ṗ)` es igual al
    numeral del valor `(runFn nil p)˙`*. -/
noncomputable def evalRunCode (p : Term) : Term :=
  eqCodeFn (runFnT (tcFn nil) (tcFn p)) (tcFn (runFn nil p))

/-- Instancia codificada de `ax_runFn_nil` con testigo `tcFn nil`, ya **computada**:
    `⊢ Prov(⌜runFn(ṅil, ⌜nil⌝) = ṅil⌝)`. (`⌜nil⌝ = termCode nil`, aún no `tcFn nil`.) -/
theorem pcc_ax_runFn_nil_computed :
    Prf (provFromCode (eqCodeFn (runFnT (tcFn nil) (termCode nil)) (tcFn nil))) :=
  prf_mp
    (prf_provCode_congr
      (prf_substfc_arith_open 0 (tcFn nil) (runFn (.var 0) nil =eq (.var 0))))
    (pcc_axiom_inst (runFn (.var 0) nil =eq (.var 0))
      (show ax_runFn_nil ∈ axioms by simp [axioms]) (tcFn nil))

/-- **BASE de la evaluación provable de `runFn`**: `⊢ Prov(⌜runFn(ṅil, ṅil) = (runFn nil nil)˙⌝)`.
    De `pcc_ax_runFn_nil_computed` transportando `⌜nil⌝ ↦ tcFn nil` (`prf_tc_zero`) y
    `tcFn nil ↦ tcFn (runFn nil nil)` (`runFn nil nil =eq nil`). -/
theorem pcc_eval_runFn_nil : Prf (provFromCode (evalRunCode nil)) := by
  have hb : Prf (termCode nil =eq tcFn nil) := prf_eq_symm prf_tc_zero
  have hr : Prf (tcFn nil =eq tcFn (runFn nil nil)) :=
    prf_eq_symm (prf_congr_tcFn (prf_runFn_nil nil))
  exact prf_mp
    (prf_provCode_congr
      (prf_congr_eqCodeFn (prf_congr_funcc2 (prf_congr_cons_tail (prf_congr_cons_head hb))) hr))
    pcc_ax_runFn_nil_computed

end ROBINSON_PlusPlus.Meta.EvalRunFnPrf

export ROBINSON_PlusPlus.Meta.EvalRunFnPrf (
  runFnT evalRunCode pcc_ax_runFn_nil_computed pcc_eval_runFn_nil
)
