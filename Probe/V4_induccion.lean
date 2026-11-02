import ROBINSON_PlusPlus
open Lean Elab Command

/-- ¿Cuantas constantes de PRODUCCION dependen de `Full.ax_induction`, y de que modulos? -/
elab "#quienusa " a:ident : command => do
  let ax := a.getId
  let env ← getEnv
  let mut hits : Array Name := #[]
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    if !((`ROBINSON_PlusPlus).isPrefixOf n) then continue
    let axs ← liftCoreM (Lean.collectAxioms n)
    if axs.contains ax then hits := hits.push n
  -- agrupar por prefijo de modulo (los dos/tres primeros componentes)
  let mut mods : Std.HashMap String Nat := {}
  for n in hits do
    let key := n.getPrefix.toString
    mods := mods.insert key ((mods.getD key 0) + 1)
  let ks := mods.toList.toArray.qsort (fun a b => b.2 < a.2)
  let mut out : Array String := #[s!"### {ax} :: {hits.size} constantes de RPP dependen de el"]
  for (k, v) in ks do
    out := out.push s!"  {k} :: {v}"
  logInfo (String.intercalate "\n" out.toList)

#quienusa ROBINSON_PlusPlus.Full.ax_induction
#quienusa ROBINSON_PlusPlus.Meta.GodelTwo.d3
#quienusa ROBINSON_PlusPlus.Minimal.Axioms.ax_axiomsCodeT_eq
