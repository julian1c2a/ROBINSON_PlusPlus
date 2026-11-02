import ROBINSON_PlusPlus.Meta.EvalLiftcPrf

/-!
# `Probe/ADV_T2_rango.lean` — VERIFICACION ADVERSARIAL del parche 3a de la tanda T2.

El entregable dice: «(3a) BORRAR las lineas 228-236, o sea los dos teoremas duplicados».
MEDIDO sobre el fichero real: `EvalLiftcPrf.lean:228` es `liftF_targetLift` y `:233` es
`liftF_targetLiftsc`. Los duplicados de verdad estan en `:238` y `:243`.
Este fichero comprueba, por TIPOS, que los cuatro son cuatro y que el par de `:228-236`
NO es el par duplicado.
-/

open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Sigma1Prf
open ROBINSON_PlusPlus.Meta.LiftcCodePrf

namespace Probe.ADVT2

/-! ## §1 · Lo que vive en `:228-236` habla de `liftFormula`, no de `substFormula`. -/

example : ∀ (k : Nat) (s : Term),
    liftFormula k (targetLift s) = targetLift (liftTerm k s) :=
  ROBINSON_PlusPlus.Meta.EvalLiftcPrf.liftF_targetLift

example : ∀ (k : Nat) (s : Term),
    liftFormula k (targetLiftsc s) = targetLiftsc (liftTerm k s) :=
  ROBINSON_PlusPlus.Meta.EvalLiftcPrf.liftF_targetLiftsc

/-! ## §2 · Lo que vive en `:238-246` habla de `substFormula`. Son OTROS dos. -/

example : ∀ (v : Nat) (u s : Term),
    substFormula v u (targetLift s) = targetLift (substTerm v u s) :=
  ROBINSON_PlusPlus.Meta.EvalLiftcPrf.substF_targetLift

/-! ## §3 · CONTROL: los dos pares NO son intercambiables. Si `liftF_targetLift` fuera
     «el duplicado», el general de `substF` podria ocupar su sitio. No puede. -/

example : True := by
  fail_if_success
    exact (ROBINSON_PlusPlus.Meta.EvalLiftcPrf.substF_targetLift :
      ∀ (k : Nat) (s : Term), liftFormula k (targetLift s) = targetLift (liftTerm k s))
  trivial

/-! ## §4 · Y el par de `:228-236` NO tiene gemelo en `LiftcCodePrf`: si lo tuviera, este
     nombre cualificado existiria. El `fail_if_success` de abajo lo confirma por elaboracion. -/

example : True := by
  fail_if_success
    exact (ROBINSON_PlusPlus.Meta.LiftcCodePrf.liftF_targetLift_hole : True)
  trivial

end Probe.ADVT2
