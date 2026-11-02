/- Probe/DOC_dump_B.lean — vuelca el nombre CORTO de toda constante de produccion (RPP+FOL). -/
import ROBINSON_PlusPlus
import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    let m := match env.getModuleIdxFor? n with
      | some idx =>
          let mods := env.allImportedModuleNames
          if h : idx.toNat < mods.size then mods[idx.toNat] else `UNKNOWN
      | none => `CURRENT
    if m.getRoot == `ROBINSON_PlusPlus || m.getRoot == `FOL then
      out := out.push s!"{n.getString!}\t{n}\t{m}"
  logInfo (String.intercalate "\n" out.toList)
