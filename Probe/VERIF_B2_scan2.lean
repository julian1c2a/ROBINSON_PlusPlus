import ROBINSON_PlusPlus

open Lean Elab Meta

def scanFor (targets : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut hits : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let s := n.toString
    unless s.startsWith "ROBINSON_PlusPlus" do continue
    let used := ci.type.getUsedConstants
    for t in targets do
      if used.contains t then
        hits := hits.push s!"[{t}]  {n}"
  let sorted := hits.qsort (fun a b => a < b)
  for h in sorted do
    logInfo m!"{h}"

open ROBINSON_PlusPlus.Meta

run_cmd Command.liftTermElabM do
  scanFor [``LiftcCodePrf.targetLift]

run_cmd Command.liftTermElabM do
  scanFor [``CodeWitnessPrf.SinWTs.argsIn, ``CodeWitnessPrf.SinWTs.isTermCodeE1]

run_cmd Command.liftTermElabM do
  scanFor [``CodeWitnessPrf.SinWTs.isTC1, ``CodeWitnessPrf.ENS.hasWit]
