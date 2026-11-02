/-
  Sonda: ¿es DESCARGABLE la hipótesis `∀ c, Prf (liftc c X =eq X)` que piden los
  `liftc_inv_fn*T` de `Probe/Ctor_generico.lean`, con lo que hay en PRODUCCIÓN?

  Producción sólo ofrece `prf_liftc_tcFn a : Prf (liftc zero (tcFn a) =eq tcFn a)`
  (`Meta/NumCodeClosedPrf.lean:134`), con el nivel FIJADO a `zero`.
  Este fichero DEBE FALLAR en el `example` marcado ⛔.
-/
import ROBINSON_PlusPlus.Meta

open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.NumCodeClosedPrf

namespace VerifLiftInv

/-- ✅ La forma que SÍ existe (nivel `zero`). -/
example (a : Term) : Prf (liftc zero (tcFn a) =eq tcFn a) := prf_liftc_tcFn a

/-- ⛔ La forma `∀ c` que piden los `liftc_inv_fn*T`: NO hay testigo en producción. -/
example (a : Term) : ∀ c, Prf (liftc c (tcFn a) =eq tcFn a) := fun _ => prf_liftc_tcFn a

end VerifLiftInv
