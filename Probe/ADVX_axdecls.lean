import ROBINSON_PlusPlus

open Lean Elab Command

elab "#axdecls2 " id:ident : command => do
  let ns := id.getId
  let env ← getEnv
  let names := (env.constants.fold (init := #[]) fun acc n ci =>
      match ci with
      | .axiomInfo _ => if ns.isPrefixOf n && !n.isInternal then acc.push n else acc
      | _ => acc).qsort (fun a b => a.toString < b.toString)
  logInfo (s!"### AXIOM DECLS bajo {ns} :: {names.size}\n"
    ++ String.intercalate "\n" (names.map (fun n => s!"DECL {n}")).toList)

#axdecls2 ROBINSON_PlusPlus
#axdecls2 FOL
