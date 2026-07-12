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

/-! ### La RECURSIÓN de `runFn` codificada (paso de la evaluación)

`prf_runFn_nil_cons` (`runFn nil (cons h t) = cons (carc h)(runFn nil t)`) codificada en forma
rastreada vía `pcc_thm_inst2` + `prf_substfc_arith_open` (patrón `pcc_ax5_computed`). Es la pieza que
el paso inductivo de la evaluación de `runFn` necesita **dentro de `Prov`** (el `runFnT` es opaco: no
evalúa por congruencia de código, hace falta la recursión reflejada). -/

/-- Versión `forall_2` (object) de `prf_runFn_nil_cons`, para codificar con `pcc_thm_inst2`. -/
theorem prf_runFn_nil_cons_forall :
    Prf (forall_2 (Formula.eq (runFn nil (cons (.var 1) (.var 0)))
      (cons (carc (.var 1)) (runFn nil (.var 0))))) :=
  Prf.gen _ (Prf.gen _ (prf_runFn_nil_cons (.var 1) (.var 0)))

/-- Congruencia de `runFnT` en ambos argumentos. -/
theorem prf_congr_runFnT {x x' y y' : Term} (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) :
    Prf (runFnT x y =eq runFnT x' y') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_congr_cons_head hy)))

/-- `substtc` atraviesa `runFnT` (funcc de 2 argumentos). -/
theorem prf_substtc_runFnT (v W x y : Term) :
    Prf (substtc v W (runFnT x y) =eq runFnT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "runFn") x y

/-- `substtc` deja invariante `termCode nil` (código cerrado; `nil = zero`). -/
theorem prf_substtc_termCode_nil (W : Term) :
    Prf (substtc zero W (termCode nil) =eq termCode nil) :=
  prf_substtc_arith_open 0 W zero

/-- **RECURSIÓN de `runFn` CODIFICADA**: `⊢ Prov(⌜runFn(⌜nil⌝, cons ḣ ṫ) = cons (carc ḣ)(runFn(⌜nil⌝, ṫ))⌝)`.
    De `pcc_thm_inst2 prf_runFn_nil_cons_forall (tcFn h)(tcFn t)`, computando el doble `substfc` sobre
    el código explícito y normalizando `liftc (tcFn h)` con (A). -/
theorem pcc_runFn_cons_code (h t : Term) :
    Prf (provFromCode (eqCodeFn (runFnT (termCode nil) (consT (tcFn h) (tcFn t)))
      (consT (carcT (tcFn h)) (runFnT (termCode nil) (tcFn t))))) := by
  let W1 : Term := liftc zero (tcFn h)
  let T : Term := tcFn t
  let BODY : Formula := Formula.eq (runFn nil (cons (.var 1) (.var 0)))
    (cons (carc (.var 1)) (runFn nil (.var 0)))
  have hin : Prf (substfc (succ zero) W1 (formCode BODY)
      =eq eqCodeFn (runFnT (termCode nil) (consT W1 (varc (numeral 0))))
                   (consT (carcT W1) (runFnT (termCode nil) (varc (numeral 0))))) :=
    prf_substfc_arith_open 1 W1 BODY
  have hA : Prf (W1 =eq tcFn h) := prf_liftc_tcFn h
  have hnorm : Prf (eqCodeFn (runFnT (termCode nil) (consT W1 (varc (numeral 0))))
                             (consT (carcT W1) (runFnT (termCode nil) (varc (numeral 0))))
      =eq eqCodeFn (runFnT (termCode nil) (consT (tcFn h) (varc (numeral 0))))
                   (consT (carcT (tcFn h)) (runFnT (termCode nil) (varc (numeral 0))))) :=
    prf_congr_eqCodeFn
      (prf_congr_runFnT (prf_refl _) (prf_congr_consT hA (prf_refl _)))
      (prf_congr_consT (prf_congr_carcT hA) (prf_refl _))
  have hout : Prf (substfc zero T
      (eqCodeFn (runFnT (termCode nil) (consT (tcFn h) (varc (numeral 0))))
                (consT (carcT (tcFn h)) (runFnT (termCode nil) (varc (numeral 0)))))
      =eq eqCodeFn (runFnT (termCode nil) (consT (tcFn h) T))
                   (consT (carcT (tcFn h)) (runFnT (termCode nil) T))) := by
    refine prf_eq_trans (prf_substfc_eq zero T _ _) ?_
    refine prf_congr_eqCodeFn ?_ ?_
    · refine prf_eq_trans
        (prf_substtc_runFnT zero T (termCode nil) (consT (tcFn h) (varc (numeral 0)))) ?_
      refine prf_congr_runFnT (prf_substtc_termCode_nil T) ?_
      refine prf_eq_trans (prf_substtc_consT zero T (tcFn h) (varc (numeral 0))) ?_
      exact prf_congr_consT (prf_substtc_tcFn T h) (prf_substtc_varc0 T)
    · refine prf_eq_trans
        (prf_substtc_consT zero T (carcT (tcFn h)) (runFnT (termCode nil) (varc (numeral 0)))) ?_
      refine prf_congr_consT ?_ ?_
      · exact prf_eq_trans (prf_substtc_carcT zero T (tcFn h))
          (prf_congr_carcT (prf_substtc_tcFn T h))
      · refine prf_eq_trans (prf_substtc_runFnT zero T (termCode nil) (varc (numeral 0))) ?_
        exact prf_congr_runFnT (prf_substtc_termCode_nil T) (prf_substtc_varc0 T)
  have hchain : Prf (substfc zero T (substfc (succ zero) W1 (formCode BODY))
      =eq eqCodeFn (runFnT (termCode nil) (consT (tcFn h) T))
                   (consT (carcT (tcFn h)) (runFnT (termCode nil) T))) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_thm_inst2 BODY prf_runFn_nil_cons_forall (tcFn h) T)

end ROBINSON_PlusPlus.Meta.EvalRunFnPrf

export ROBINSON_PlusPlus.Meta.EvalRunFnPrf (
  runFnT evalRunCode pcc_ax_runFn_nil_computed pcc_eval_runFn_nil
  prf_runFn_nil_cons_forall prf_congr_runFnT prf_substtc_runFnT prf_substtc_termCode_nil
  pcc_runFn_cons_code
)
