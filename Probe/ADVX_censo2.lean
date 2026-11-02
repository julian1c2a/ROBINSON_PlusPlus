import ROBINSON_PlusPlus

/-! Listado NOMINAL por bucket de EvalLiftcPrf (solo lectura). -/

open Lean Elab Command

def constsInNs2 (env : Environment) (ns : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if ns.isPrefixOf n && n != ns && !n.isInternal then acc.push n else acc

elab "#lista " id:ident : command => do
  let ns := id.getId
  let env ← getEnv
  let names := (constsInNs2 env ns).qsort (fun a b => a.toString < b.toString)
  let mut lines : Array String := #[s!"### NS {ns}"]
  for n in names do
    let axs ← liftCoreM (Lean.collectAxioms n)
    let l := (axs.map (·.toString)).toList
    let tag :=
      if l.contains "ROBINSON_PlusPlus.Meta.Representability2Prf.prf_axiomsCodeT_eq" then "CUATRO"
      else s!"MENOS({l.length})"
    let kind := match env.find? n with
      | some (.thmInfo _) => "thm"
      | some (.defnInfo _) => "def"
      | some (.axiomInfo _) => "AXIOM"
      | _ => "otro"
    lines := lines.push s!"  {tag} [{kind}] {n}"
  logInfo (String.intercalate "\n" lines.toList)

#lista ROBINSON_PlusPlus.Meta.EvalLiftcPrf

-- Los 13 que imprime el bloque CONTROL DE FOOTPRINT (:671-683)
#print axioms ROBINSON_PlusPlus.Meta.CodeWitnessPrf.SinWTs.prf_isTermCodeE1_of_In
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_targetLift_real
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.CRIT_hasWit_descenso
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.prf_nil_or_cons
#print axioms ROBINSON_PlusPlus.Meta.EvalLiftcPrf.pcc_eval_liftc
