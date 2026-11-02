import ROBINSON_PlusPlus
open Lean Elab Command
elab "#axgroups " id:ident : command => do
  let ns := id.getId
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if ns.isPrefixOf n && n != ns && !n.isInternal then acc.push n else acc
  let mut worst : Array String := #[]
  let mut tot := 0
  for n in names do
    let axs ← liftCoreM (Lean.collectAxioms n)
    tot := tot + 1
    if axs.size > 4 then
      worst := worst.push s!"GORDO {n} :: [{String.intercalate ", " (axs.map (·.toString)).toList}]"
  let body := String.intercalate "\n" worst.toList
  logInfo (s!"{ns} :: {tot} constantes; con MAS de 4 axiomas: {worst.size}\n" ++ body)
#axgroups ROBINSON_PlusPlus.Meta.CodeWitnessPrf
