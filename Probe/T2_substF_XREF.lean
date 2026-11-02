import ROBINSON_PlusPlus.Meta

/-!
# `Probe/T2_substF_XREF.lean` — control cruzado de `Probe/T2_substF.lean`

`T2_substF.lean` mide el DESCENSO con copias byte-a-byte de `liftcT`, `targetLift` y
`substTerm_termCode` (no puede importar `LiftcCodePrf` sin invalidar la medida). Este
fichero cierra el hueco por el otro lado: con el barrel entero, comprueba contra las
constantes REALES que el corolario propuesto y el lema de produccion son EL MISMO tipo.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.LiftcCodePrf

namespace Probe.T2XREF

/-- El general REAL (`Meta/EvalLiftcPrf.lean:228`), instanciado en `v:=0, u:=t, s:=#0`,
    HABITA el tipo del particular REAL (`Meta/LiftcCodePrf.lean:790`) sin conversion. -/
theorem hole_desde_el_general_real (t : Term) :
    substFormula 0 t (provFromCode (eqc (liftcT (termCode zero) (tcFn (.var 0)))
        (tcFn (liftc zero (.var 0)))))
      = targetLift t :=
  ROBINSON_PlusPlus.Meta.EvalLiftcPrf.substF_targetLift 0 t (.var 0)

/-- Y al reves: los DOS TERMINOS de produccion son defeq, luego el particular es
    literalmente la instancia del general. -/
theorem prod_es_la_instancia (t : Term) :
    ROBINSON_PlusPlus.Meta.LiftcCodePrf.substF_targetLift_hole t
      = ROBINSON_PlusPlus.Meta.EvalLiftcPrf.substF_targetLift 0 t (.var 0) := rfl

end Probe.T2XREF

#print axioms Probe.T2XREF.hole_desde_el_general_real
#print axioms Probe.T2XREF.prod_es_la_instancia
