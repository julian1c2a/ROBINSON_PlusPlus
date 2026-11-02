import ROBINSON_PlusPlus

/-!
# VERIFICACION ADVERSARIAL — censo propio, independiente del auditor.
Solo lectura: no define nada del arbol.
-/

open Lean Elab Command

/-- La BASE SANCIONADA tal y como la publica `doc/book/fragmentos.json`. -/
def baseSancionada : List String :=
  [ "propext", "Classical.choice", "Quot.sound",
    "FOL.MetaRules.imp_intro", "FOL.MetaRules.gen", "FOL.MetaRules.raa",
    "FOL.MetaRules.dne", "FOL.MetaRules.or_elim", "FOL.MetaRules.ex_elim",
    "ROBINSON_PlusPlus.Full.Induction.ax_induction",
    "ROBINSON_PlusPlus.Full.Lists.ax_list_induction",
    "ROBINSON_PlusPlus.Full.Mod2.ax_mod2_alternation",
    "ROBINSON_PlusPlus.Minimal.Theorems.Block8.ax_p_tfa",
    "ROBINSON_PlusPlus.Minimal.Axioms.ax_axiomsCodeT_eq",
    "ROBINSON_PlusPlus.Minimal.Axioms.prf_axiomsCodeT_eq",
    "ROBINSON_PlusPlus.Meta.GodelTwo.d3" ]

/-- Los TRES de Lean: "net-0 puro" segun el glosario del proyecto. -/
def losTres : List String := ["propext", "Classical.choice", "Quot.sound"]

def shorten (s : String) : String :=
  let s := s.replace "ROBINSON_PlusPlus.Meta." ""
  let s := s.replace "ROBINSON_PlusPlus.Full." ""
  let s := s.replace "ROBINSON_PlusPlus.Minimal." ""
  s.replace "FOL.MetaRules." "MR."

def sigOf (axs : Array Name) : String :=
  let ss := (axs.map (fun n => shorten n.toString)).qsort (· < ·)
  "[" ++ String.intercalate ", " ss.toList ++ "]"

/-- Censo AGRUPADO: firmas de footprint y cuantas constantes tiene cada una. -/
elab "#grupos " id:ident : command => do
  let ns := id.getId
  let env ← getEnv
  let names := (env.constants.fold (init := #[]) fun acc n _ =>
      if ns.isPrefixOf n && n != ns && !n.isInternal then acc.push n else acc).qsort
        (fun a b => a.toString < b.toString)
  let mut buckets : Std.HashMap String (Array Name) := {}
  let mut fuera : Array String := #[]
  for n in names do
    let axs ← liftCoreM (Lean.collectAxioms n)
    -- ¿algun axioma FUERA de la base sancionada?
    for a in axs do
      if !(baseSancionada.contains a.toString) then
        fuera := fuera.push s!"!! {n} usa {a}"
    let s := sigOf axs
    buckets := buckets.insert s ((buckets.getD s #[]).push n)
  let mut out : Array String := #[s!"### NS {ns} :: {names.size} constantes"]
  let ks := (buckets.toList.map (fun p => (p.1, p.2))).toArray.qsort
              (fun a b => b.2.size < a.2.size)
  for (k, v) in ks do
    out := out.push s!"  N={v.size} :: {k}"
    -- lista los nombres solo si el grupo es pequeno o se sale de los tres
    if v.size ≤ 25 then
      out := out.push ("        " ++ String.intercalate ", " (v.map (fun n => n.getString!)).toList)
  if fuera.isEmpty then
    out := out.push "  ✔ TODO dentro de base_sancionada"
  else
    out := out ++ fuera
  logInfo (String.intercalate "\n" out.toList)

/-- Footprint exacto de constantes concretas (para contrastar citas del auditor). -/
elab "#fp " ids:ident+ : command => do
  let mut out : Array String := #[]
  for id in ids do
    let n := id.getId
    let axs ← liftCoreM (Lean.collectAxioms n)
    let n3 := (axs.filter (fun a => !losTres.contains a.toString)).size
    out := out.push s!"FP {n} :: {axs.size} ax, extra-a-los-tres={n3} :: {sigOf axs}"
  logInfo (String.intercalate "\n" out.toList)

#grupos ROBINSON_PlusPlus.Meta.CodeNatInjPrf
#grupos ROBINSON_PlusPlus.Meta.EvalPredPrf
#grupos ROBINSON_PlusPlus.Meta.StrongInductionPrf
#grupos ROBINSON_PlusPlus.Meta.MpCodePrf
#grupos ROBINSON_PlusPlus.Meta.EvalLiftcPrf
#grupos ROBINSON_PlusPlus.Meta.LiftcCodePrf
