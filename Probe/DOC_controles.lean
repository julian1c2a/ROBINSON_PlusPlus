/-
Probe/DOC_controles.lean — controles COMPILADOS de la auditoria de existencia.
Cada `example` mide una afirmacion concreta de un docstring del frente.
-/
import ROBINSON_PlusPlus

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.CodeCtorKit
open ROBINSON_PlusPlus.Meta.EvalPredPrf

set_option maxHeartbeats 1000000

/-! ## C1 · EvalPredPrf §5b: «`varc x = ⟨0,x⟩` es EXACTAMENTE `unT 0`, por `rfl`
       — ver `varc_es_un0`». ¿Es `varc n = unT 0 n` por `rfl`? -/

example (n : Term) : True := by
  fail_if_success exact (rfl : varc n = unT 0 n)
  trivial

/-- Lo que SI dice el lema citado: la forma ⟨0,x⟩ con `cons`, no `unT 0`. -/
example (n : Term) : varc n = cons (numeralM 0) (cons n nil) :=
  ROBINSON_PlusPlus.Meta.EvalPredPrf.varc_es_un0 n

/-! ## C2 · LiftcCodePrf §11: el enunciado que anuncia para `DESCENSO`. -/

#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO
#check @ROBINSON_PlusPlus.Meta.EvalLiftcPrf.DESCENSO_lista

/-! ## C3 · EvalLiftcPrf §4: ¿`SinWTs.impT` y `ENS.impT` son la misma pieza? -/

example : @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.impT
        = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.impT := rfl
example : @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_or_elim_imp
        = @ROBINSON_PlusPlus.Meta.CodeWitnessPrf.ENS.prf_or_elim_imp := rfl

/-! ## C4 · CodeNatInjPrf: los DOS `numeral` y el puente. -/

#check @ROBINSON_PlusPlus.Full.numeral
#check @ROBINSON_PlusPlus.Meta.Godel.numeral
#check @ROBINSON_PlusPlus.Meta.CodeNatInjPrf.num_bridge
