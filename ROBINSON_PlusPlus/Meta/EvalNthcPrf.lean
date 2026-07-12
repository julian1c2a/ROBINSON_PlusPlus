/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.EvalRunFnPrf

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
open ROBINSON_PlusPlus.Meta.EvalRunFnPrf

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ROBINSON_PlusPlus.Meta.EvalNthcPrf

/-!
## META — NIVEL D real (§35, arranque): evaluación ACOTADA de `nthc`

Para `hI_dot` vía `boundedCarcIn` (`∃i<lenc p. carc(nthc p i) = ⌜φ⌝`) hace falta puentear el término
simbólico `nthc(ṗ, ı̇)` con el valor `(nthc p i)˙`. A diferencia de `+` (total), `nthc` es **parcial**
(sólo definido sobre `cons`/índices en rango), así que la evaluación es **acotada** (`i < lenc p`):

```text
⊢ (i < lenc p) → Prov( ⌜ nthc(ṗ, ı̇) = (nthc p i)˙ ⌝ )
```

Se prueba por inducción de listas sobre `p` con análisis de casos sobre `i` (`0`/`σj`), reflejando las
dos **ecuaciones codificadas** de `nthc`:

* `ax_nthc_zero` (`forall_2`): `pcc_nthc_zero_code` (vía `pcc_axiom_inst2`) — **hecho aquí**.
* `ax_nthc_succ` (`forall_3`): `pcc_nthc_succ_code` (vía `pcc_axiom_inst3`, §MpCodePrf) — pendiente.

**Este módulo entrega la ecuación `zero`.** El `succ` (`substfc` triple) y la inducción acotada quedan
como siguiente ladrillo. Nota: `nthc` es total sobre índices en rango, así que **no** tiene la
partialidad de `carc` (esa se resuelve con `chainOk` → la línea es `cons`).
-/

/-- Constructor de código del término `nthc x y`: `⟨1, ⌜nthc⌝, [x, y]⟩`. -/
def nthcT (x y : Term) : Term := funcc (strCode "nthc") (cons x (cons y nil))

/-- Congruencia de `nthcT` en ambos argumentos. -/
theorem prf_congr_nthcT {x x' y y' : Term} (hx : Prf (x =eq x')) (hy : Prf (y =eq y')) :
    Prf (nthcT x y =eq nthcT x' y') :=
  prf_congr_funcc2 (prf_eq_trans (prf_congr_cons_head hx)
    (prf_congr_cons_tail (prf_congr_cons_head hy)))

/-- `substtc` atraviesa `nthcT` (funcc de 2 argumentos). -/
theorem prf_substtc_nthcT (v W x y : Term) :
    Prf (substtc v W (nthcT x y) =eq nthcT (substtc v W x) (substtc v W y)) :=
  prf_substtc_funcc2 v W (strCode "nthc") x y

/-- **Ecuación `zero` de `nthc` CODIFICADA**: `⊢ Prov(⌜nthc(cons ḣ ṫ, ⌜0⌝) = ḣ⌝)`.
    De `pcc_axiom_inst2` de `ax_nthc_zero` (testigos `tcFn h`, `tcFn t`), computando el doble
    `substfc` sobre el código explícito (patrón `pcc_ax5_computed`). -/
theorem pcc_nthc_zero_code (h t : Term) :
    Prf (provFromCode (eqCodeFn (nthcT (consT (tcFn h) (tcFn t)) (termCode zero)) (tcFn h))) := by
  let W1 : Term := liftc zero (tcFn h)
  let T : Term := tcFn t
  let BODY : Formula := nthc (cons (.var 1) (.var 0)) zero =eq (.var 1)
  have hin : Prf (substfc (succ zero) W1 (formCode BODY)
      =eq eqCodeFn (nthcT (consT W1 (varc (numeral 0))) (termCode zero)) W1) :=
    prf_substfc_arith_open 1 W1 BODY
  have hA : Prf (W1 =eq tcFn h) := prf_liftc_tcFn h
  have hnorm : Prf (eqCodeFn (nthcT (consT W1 (varc (numeral 0))) (termCode zero)) W1
      =eq eqCodeFn (nthcT (consT (tcFn h) (varc (numeral 0))) (termCode zero)) (tcFn h)) :=
    prf_congr_eqCodeFn
      (prf_congr_nthcT (prf_congr_consT hA (prf_refl _)) (prf_refl _)) hA
  have hout : Prf (substfc zero T
      (eqCodeFn (nthcT (consT (tcFn h) (varc (numeral 0))) (termCode zero)) (tcFn h))
      =eq eqCodeFn (nthcT (consT (tcFn h) T) (termCode zero)) (tcFn h)) := by
    refine prf_eq_trans (prf_substfc_eq zero T _ _) ?_
    refine prf_congr_eqCodeFn ?_ (prf_substtc_tcFn T h)
    refine prf_eq_trans
      (prf_substtc_nthcT zero T (consT (tcFn h) (varc (numeral 0))) (termCode zero)) ?_
    refine prf_congr_nthcT ?_ (prf_substtc_termCode_nil T)
    refine prf_eq_trans (prf_substtc_consT zero T (tcFn h) (varc (numeral 0))) ?_
    exact prf_congr_consT (prf_substtc_tcFn T h) (prf_substtc_varc0 T)
  have hchain : Prf (substfc zero T (substfc (succ zero) W1 (formCode BODY))
      =eq eqCodeFn (nthcT (consT (tcFn h) T) (termCode zero)) (tcFn h)) :=
    prf_eq_trans (prf_congr_substfc_arg3 (prf_eq_trans hin hnorm)) hout
  exact prf_mp (prf_provCode_congr hchain)
    (pcc_axiom_inst2 BODY (show ax_nthc_zero ∈ axioms by simp [axioms]) (tcFn h) T)

end ROBINSON_PlusPlus.Meta.EvalNthcPrf

export ROBINSON_PlusPlus.Meta.EvalNthcPrf (
  nthcT prf_congr_nthcT prf_substtc_nthcT pcc_nthc_zero_code
)
