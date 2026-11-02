/- ADVERSARIAL: ¿es `prf_congr_liftc` AMBIGUO a nivel RAIZ tras importar
   CodeWitnessPrf (export SinWTs) y NumCodeClosedPrf (export propio)? -/
import ROBINSON_PlusPlus.Meta.SubstfcCodePrf
import ROBINSON_PlusPlus.Meta.EvalLiftcPrf
open ROBINSON_PlusPlus.Minimal.Axioms ROBINSON_PlusPlus.Meta.Godel
open ROBINSON_PlusPlus.Meta.Provability ROBINSON_PlusPlus.Meta.Hilbert

-- Si resolviera a UNA sola, esto compila. Si es ambiguo, error.
example {a b : Term} (c : Term) (h : Prf (a =eq b)) : Prf (liftc c a =eq liftc c b) :=
  prf_congr_liftc h
