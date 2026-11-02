import ROBINSON_PlusPlus

/-!
# VERIFICACION ADVERSARIAL del censo de footprint (solo lectura)
Agrupa las constantes de cada namespace por su firma de axiomas.
-/

open Lean Elab Command

def constsInNs' (env : Environment) (ns : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if ns.isPrefixOf n && n != ns && !n.isInternal then acc.push n else acc

/-- Firma agrupada: cuantas constantes por footprint, y nombres si el footprint
    sale del conjunto {propext, Classical.choice, Quot.sound, prf_axiomsCodeT_eq}. -/
elab "#agrupa " id:ident : command => do
  let ns := id.getId
  let env ← getEnv
  let names := (constsInNs' env ns).qsort (fun a b => a.toString < b.toString)
  let base : List String :=
    ["propext", "Classical.choice", "Quot.sound",
     "ROBINSON_PlusPlus.Meta.Representability2Prf.prf_axiomsCodeT_eq"]
  let mut buckets : Array (String × Nat) := #[]
  let mut fuera : Array String := #[]
  for n in names do
    let axs ← liftCoreM (Lean.collectAxioms n)
    let l := (axs.map (·.toString)).toList
    let key := String.intercalate ", " l
    if l.any (fun a => !base.contains a) then
      fuera := fuera.push s!"  FUERA-DE-BASE {n} :: [{key}]"
    match buckets.findIdx? (fun p => p.1 == key) with
    | some i => buckets := buckets.set! i (key, buckets[i]!.2 + 1)
    | none   => buckets := buckets.push (key, 1)
  let mut lines : Array String := #[s!"### NS {ns} :: {names.size} constantes"]
  for (k, c) in buckets do
    lines := lines.push s!"  [{c}x] [{k}]"
  lines := lines ++ fuera
  logInfo (String.intercalate "\n" lines.toList)

#agrupa ROBINSON_PlusPlus.Meta.LiftcCodePrf
#agrupa ROBINSON_PlusPlus.Meta.EvalLiftcPrf
#agrupa ROBINSON_PlusPlus.Meta.CodeNatInjPrf
#agrupa ROBINSON_PlusPlus.Meta.EvalPredPrf
#agrupa ROBINSON_PlusPlus.Meta.MpCodePrf
#agrupa ROBINSON_PlusPlus.Meta.StrongInductionPrf
#agrupa ROBINSON_PlusPlus.Meta.CodeWitnessPrf

-- El puente de §0 de EvalLiftcPrf que NO es `rfl`: ¿lo seria?
example (a b : ROBINSON_PlusPlus.Minimal.Syntax.Term) :
    ROBINSON_PlusPlus.Minimal.Axioms.eqc a b
      = ROBINSON_PlusPlus.Meta.Sigma1AtomPrf.eqCodeFn a b := rfl
