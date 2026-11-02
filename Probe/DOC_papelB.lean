/- # DOC_papelB — auditoria de SIGNIFICADO (papel/consecuencia) de los docstrings del frente
       lake env lean Probe/DOC_papelB.lean
   NO toca produccion: solo COMPRUEBA enunciados.
-/
import ROBINSON_PlusPlus.Meta

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.ReprPrf ROBINSON_PlusPlus.Meta.NumListPrf
open ROBINSON_PlusPlus.Meta.LiftcCodePrf ROBINSON_PlusPlus.Meta.EvalLiftcPrf
open ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs

namespace DOCpapel

/-! ## A · `Meta/LiftcCodePrf.lean:986-1004` (§11) dice que el RESIDUO es, «con nombre y
    enunciado exactos»,

        DESCENSO : ∀ w X, Prf (isTC1 w X) → Prf (targetLiftsc (nthc X (numeralM 2)))

    El `DESCENSO` que existe (ya en PRODUCCION, `Meta/EvalLiftcPrf.lean:504`) tiene OTRA
    conclusion: `targetLift X`. -/

#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO
#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista
#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_imp

-- (A1) El tipo que la §11 anuncia NO es el de `DESCENSO`.
example : True := by
  fail_if_success
    exact (ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO :
      ∀ w X : Term, Prf (isTC1 w X) → Prf (targetLiftsc (nthc X (numeralM 2))))
  trivial

-- (A2) Y tampoco el de `DESCENSO_lista` / `DESCENSO_imp`.
example : True := by
  fail_if_success
    exact (ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista :
      ∀ w X : Term, Prf (isTC1 w X) → Prf (targetLiftsc (nthc X (numeralM 2))))
  trivial

-- (A3) Las dos conclusiones no son la misma formula (ni por `rfl`).
example (X : Term) : True := by
  fail_if_success
    exact (rfl : targetLift X = targetLiftsc (nthc X (numeralM 2)))
  trivial

-- (A4) El tipo REAL de `DESCENSO`, aceptado por ascripcion: la conclusion es `targetLift`.
example : ∀ w s : Term, Prf (isTC1 w s) → Prf (targetLift s) :=
  ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO

/-! ## B · `Meta/LiftcCodePrf.lean:956` llama a `refl_isTermCodeE1_imp` «EL RESULTADO CENTRAL
    DE ESTE MODULO». Su SEGUNDA premisa es `targetLiftsc (nthc X 2̄)`, o sea justo lo que el
    descenso fabrica; y quien de verdad consume el modulo aguas abajo (el paso inductivo
    `EvalLiftcPrf.PHI_step`) usa `refl_shapeUn_imp` / `refl_shapeBin_imp`, no este. -/

#check @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_isTermCodeE1_imp
#check @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeUn_imp
#check @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_shapeBin_imp

/-! ## C · `Meta/EvalLiftcPrf.lean:83,595`: «`DESCENSO_hasWit` es la forma consumible rio
    abajo». Se comprueba que el `hLift` que pide `paso2_caso_forall`
    (`sondeos/Paso2CasoForall.lean:507`) sale de `DESCENSO_hasWit` bajo la guarda `hasWit s`,
    y que `targetLift s` es literalmente ese `hLift` (por `rfl`). -/

example (s : Term) :
    targetLift s
      = provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))) := rfl

example (s : Term) :
    Prf (Formula.impl (ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.hasWit s)
      (provFromCode (eqc (liftcT (termCode zero) (tcFn s)) (tcFn (liftc zero s))))) :=
  ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_hasWit s

end DOCpapel
