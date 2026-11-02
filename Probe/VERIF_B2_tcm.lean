import ROBINSON_PlusPlus.Meta.LiftcCodePrf
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Provability
open ROBINSON_PlusPlus.Meta.LiftcCodePrf

/-! ¿`CONTROL_no_vacuo` (sobre `termCodeM`) es ya `refl_termCode` (sobre `termCode`)? -/

-- (a) `termCodeM` y `termCode` NO son la misma funcion.
example : True := by
  fail_if_success
    exact (rfl : (termCodeM : Term → Term) = (termCode : Term → Term))
  trivial

-- (b) ni el objetivo del control se descarga con el lema de produccion.
example : True := by
  fail_if_success
    exact (fun t => refl_termCode t :
      ∀ t : Term, Prf (targetLift (termCodeM t)))
  trivial

#check @ROBINSON_PlusPlus.Meta.LiftcCodePrf.refl_termCode
