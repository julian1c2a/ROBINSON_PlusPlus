import ROBINSON_PlusPlus
open Lean Elab Command
/-- ¿Que constantes de RPP arrastran un axioma NO inventariado en AXIOMS.md? -/
elab "#reach" : command => do
  let env ← getEnv
  let sospechosos : Array Name :=
    #[`FOL.Theorems.Neg.dne, `FOL.Theorems.Quantifiers.forall_not_impl_exists_not]
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if (`ROBINSON_PlusPlus).isPrefixOf n && !n.isInternal then acc.push n else acc
  let mut hits : Array String := #[]
  let mut fol : Array String := #[]
  for n in names do
    let axs ← liftCoreM (Lean.collectAxioms n)
    if sospechosos.any (fun s => axs.contains s) then
      hits := hits.push s!"HIT {n} :: [{String.intercalate ", " (axs.map (·.toString)).toList}]"
    if axs.any (fun a => (`FOL).isPrefixOf a) then
      fol := fol.push n.toString
  let body := String.intercalate "\n" hits.toList
  logInfo (s!"RPP: {names.size} constantes | tocan un axioma FOL: {fol.size} | tocan un axioma FOL NO INVENTARIADO: {hits.size}\n" ++ body)
#reach
