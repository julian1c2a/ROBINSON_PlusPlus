/- ¿`argsIn` de la vía sin-wTs ES `boundedAllIn` de producción?
   Si lo es, el `∀` anidado se puede DOTAR COMO ÁTOMO (`allIn`), que es la idea #2 de A3
   (`inFormCodeFn`) — y el "muro nuevo" se disuelve antes de existir. -/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Hilbert ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.BoundedInPrf ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf

namespace ArgsInEsAllIn

/-- La definición de la vía sin‑`wTs` (copia literal de `Probe/CritLift_sinwts.lean:109‑114`). -/
def argsInBody (wT Y : Term) : Formula :=
  Formula.impl (lt (.var 0) (liftTerm 0 (lenc Y)))
    (In (nthc (liftTerm 0 Y) (.var 0)) (liftTerm 0 wT))

def argsIn (wT Y : Term) : Formula := Formula.forall (argsInBody wT Y)

/-- **LA COMPROBACIÓN**: ¿es literalmente `boundedAllIn` de producción
    (`Meta/ChainOkBoundedPrf.lean:242`)? -/
theorem argsIn_es_boundedAllIn (wT Y : Term) : argsIn wT Y = boundedAllIn wT Y := rfl

/-- Y producción YA tiene el puente con el ÁTOMO `allIn`
    (`Meta/ChainOkBoundedPrf.lean:415`). -/
theorem argsIn_iff_allIn (wT Y : Term) : Prf (allIn wT Y ⇔ argsIn wT Y) := by
  rw [argsIn_es_boundedAllIn]
  exact prf_allIn_iff_boundedAllIn wT Y

/-- Las dos direcciones, sueltas. -/
theorem prf_argsIn_of_allIn (wT Y : Term) : Prf (Formula.impl (allIn wT Y) (argsIn wT Y)) := by
  rw [argsIn_es_boundedAllIn]; exact prf_and_elim_left (prf_allIn_iff_boundedAllIn wT Y)

theorem prf_allIn_of_argsIn (wT Y : Term) : Prf (Formula.impl (argsIn wT Y) (allIn wT Y)) := by
  rw [argsIn_es_boundedAllIn]; exact prf_and_elim_right (prf_allIn_iff_boundedAllIn wT Y)

/-- ⚠️ Y `allIn` es un **ÁTOMO**, luego su cuerpo dotado **no tiene binder**. -/
theorem allIn_es_atomo (c L : Term) : allIn c L = Formula.atom "allIn" [c, L] := rfl

end ArgsInEsAllIn

#print axioms ArgsInEsAllIn.argsIn_es_boundedAllIn
#print axioms ArgsInEsAllIn.argsIn_iff_allIn
#print axioms ArgsInEsAllIn.prf_argsIn_of_allIn
#print axioms ArgsInEsAllIn.prf_allIn_of_argsIn
