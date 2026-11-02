import ROBINSON_PlusPlus.Meta.LiftcCodePrf
import ROBINSON_PlusPlus.Meta.CodeWitnessPrf
import ROBINSON_PlusPlus.Meta.StrongInductionPrf
import ROBINSON_PlusPlus.Meta.CantorMonoPrf
import ROBINSON_PlusPlus.Meta.BoundedInPrf
import ROBINSON_PlusPlus.Meta.ChainPrf
import ROBINSON_PlusPlus.Meta.EvalListPrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.EvalRunFnPrf
import ROBINSON_PlusPlus.Meta.Sigma1AtomPrf
import ROBINSON_PlusPlus.Meta.Sigma1Prf
import ROBINSON_PlusPlus.Meta.NumCodeClosedPrf
import ROBINSON_PlusPlus.Meta.DotConsPrf
import ROBINSON_PlusPlus.Meta.SubstCodeOpenPrf
import ROBINSON_PlusPlus.Meta.TcArithPrf
import ROBINSON_PlusPlus.Meta.NatArithPrf
import ROBINSON_PlusPlus.Meta.TrackedCorePrf
import ROBINSON_PlusPlus.Meta.Delta0ReflectPrf
import ROBINSON_PlusPlus.Meta.DerivCondPrf
import ROBINSON_PlusPlus.Meta.MpCodePrf
import ROBINSON_PlusPlus.Meta.CodeCtorKit
import ROBINSON_PlusPlus.Meta.EvalNthcPrf
import ROBINSON_PlusPlus.Meta.EvalLtPrf
import ROBINSON_PlusPlus.Meta.EvalArithPrf
import ROBINSON_PlusPlus.Meta.EvalCarcNthcPrf
import ROBINSON_PlusPlus.Meta.NumListPrf
import ROBINSON_PlusPlus.Meta.ChainOkBoundedPrf
import ROBINSON_PlusPlus.Meta.Sigma1CorePrf
import ROBINSON_PlusPlus.Meta.RunFnBoundedPrf
import ROBINSON_PlusPlus.Meta.HilbertDeduction
import ROBINSON_PlusPlus.Meta.Provability

open Lean Elab Meta

/-- Escanea TODO el entorno importado y lista las constantes de `ROBINSON_PlusPlus`
    cuyo TIPO menciona alguno de los simbolos dados. -/
def scanFor (targets : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut hits : Array (Name × Name) := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let s := n.toString
    unless s.startsWith "ROBINSON_PlusPlus" do continue
    -- ignorar los propios helpers de este fichero
    let used := ci.type.getUsedConstants
    for t in targets do
      if used.contains t then
        hits := hits.push (t, n)
  let mut sorted := hits.qsort (fun a b => a.1.toString ++ a.2.toString < b.1.toString ++ b.2.toString)
  for (t, n) in sorted do
    logInfo m!"[{t}]  {n}"

open ROBINSON_PlusPlus.Meta

run_cmd Command.liftTermElabM do
  scanFor [``LiftcCodePrf.targetLiftsc]

run_cmd Command.liftTermElabM do
  scanFor [``CodeWitnessPrf.SinWTs.consOk]

run_cmd Command.liftTermElabM do
  scanFor [``StrongInductionPrf.PSI]
