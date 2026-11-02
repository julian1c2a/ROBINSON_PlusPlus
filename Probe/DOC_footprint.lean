import ROBINSON_PlusPlus

/-!
# AUDITORIA DE FOOTPRINT — censo mecanico de `#print axioms`

Sondeo de SOLO LECTURA. No define nada del arbol; solo recorre `env.constants`.
-/

open Lean Elab Command

/-- Todas las constantes (no internas) cuyo nombre cuelga de `ns`. -/
def constsInNs (env : Environment) (ns : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if ns.isPrefixOf n && n != ns && !n.isInternal then acc.push n else acc

/-- Censo: para cada constante del namespace, su footprint literal de axiomas. -/
elab "#axcensus " id:ident : command => do
  let ns := id.getId
  let env ← getEnv
  let names := (constsInNs env ns).qsort (fun a b => a.toString < b.toString)
  let mut lines : Array String := #[s!"### NS {ns} :: {names.size} constantes"]
  for n in names do
    let axs ← liftCoreM (Lean.collectAxioms n)
    lines := lines.push s!"AX {n} :: [{String.intercalate ", " (axs.map (·.toString)).toList}]"
  logInfo (String.intercalate "\n" lines.toList)

/-- Censo de declaraciones `axiom` REALES bajo un namespace. -/
elab "#axdecls " id:ident : command => do
  let ns := id.getId
  let env ← getEnv
  let names := (env.constants.fold (init := #[]) fun acc n ci =>
      match ci with
      | .axiomInfo _ => if ns.isPrefixOf n && !n.isInternal then acc.push n else acc
      | _ => acc).qsort (fun a b => a.toString < b.toString)
  let body := String.intercalate "\n" (names.map (fun n => s!"DECL {n}")).toList
  logInfo (s!"### AXIOM DECLS bajo {ns} :: {names.size}\n" ++ body)

#axdecls ROBINSON_PlusPlus
#axdecls FOL

#axcensus ROBINSON_PlusPlus.Meta.LiftcCodePrf
#axcensus ROBINSON_PlusPlus.Meta.EvalLiftcPrf
#axcensus ROBINSON_PlusPlus.Meta.CodeNatInjPrf
#axcensus ROBINSON_PlusPlus.Meta.EvalPredPrf
#axcensus ROBINSON_PlusPlus.Meta.MpCodePrf
#axcensus ROBINSON_PlusPlus.Meta.StrongInductionPrf
