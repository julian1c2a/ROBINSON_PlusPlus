/-
# ANEXO 2 de `Probe/B3_substtc_dedup.lean` — el §13 se puede matar SIN ciclo de imports.

El hallazgo del fichero principal (§C.3 / §D) es que el §13 del sondeo esta muerto porque
`Meta/EvalPredPrf.lean` ya prueba `pcc_eval_pred` **sin la guarda `v < n`**. Para poder
consumirlo, el modulo promovido `Meta/EvalSubsttcPrf.lean` tiene que importar `EvalPredPrf`
ademas de `EvalLiftcPrf`.

⚠️ Esa es justo la pregunta que el ADR-019 obliga a hacer: **¿hay ciclo?** No lo hay, y se
comprueba aqui: `EvalPredPrf` y `EvalLiftcPrf` son AMBAS hojas (el unico modulo que las importa
es el barrel `ROBINSON_PlusPlus/Meta.lean`), asi que un modulo nuevo puede importar las dos.
Este fichero importa **exactamente esas dos** —sin el barrel— y cierra la pieza que mata el §13.

    lake env lean Probe/B3_substtc_dedup_PREDIMPORT.lean
-/
import ROBINSON_PlusPlus.Meta.EvalLiftcPrf
import ROBINSON_PlusPlus.Meta.EvalPredPrf

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.EvalPredPrf
open FOL

namespace ANEXO_PREDIMPORT

/-- La pieza SIN guarda, ya en produccion. Lo unico que el sondeo necesitaba de todo su §13. -/
theorem pred_dotado (n : Term) :
    Prf (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n)))) := pcc_eval_pred n

/-- Y su debilitamiento a la forma GUARDADA que el sondeo llama `PredHyp` — una linea. -/
theorem pred_dotado_guardado (v n : Term) :
    Prf (Formula.impl (lt v n) (provFromCode (eqc (predcT (tcFn n)) (tcFn (pred n))))) :=
  prf_deduction (prf_to_prfH (pcc_eval_pred n) _)

/-- La otra pieza del §13: `pcc_pred_succ_code` es esta con `w := tcFn m`. -/
theorem pred_succ_dotado (m : Term) :
    Prf (provFromCode (eqCodeFn (predcT (succcT (tcFn m))) (tcFn m))) :=
  pcc_ax26_computed (tcFn m)

/-- Y `liftT_predcode` es `liftTerm_evalPredCode` desplegado. -/
theorem liftT_pred (k : Nat) (n : Term) :
    liftTerm k (eqc (predcT (tcFn n)) (tcFn (pred n)))
      = eqc (predcT (tcFn (liftTerm k n))) (tcFn (pred (liftTerm k n))) :=
  liftTerm_evalPredCode k n

/-- CONTROL: `EvalLiftcPrf` tambien esta disponible en el mismo fichero — no hay ciclo. -/
example (w s : Term) (h : Prf (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.isTC1 w s)) :
    Prf (ROBINSON_PlusPlus.Meta.LiftcCodePrf.targetLift s) :=
  ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftc w s h

end ANEXO_PREDIMPORT

#print axioms ANEXO_PREDIMPORT.pred_dotado
#print axioms ANEXO_PREDIMPORT.pred_dotado_guardado
#print axioms ANEXO_PREDIMPORT.pred_succ_dotado
#print axioms ANEXO_PREDIMPORT.liftT_pred
