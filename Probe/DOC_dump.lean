/-
Probe/DOC_dump.lean — volcado COMPLETO de `env.constants` (RPP+FOL): nombre :: modulo.
Sirve de base para comparar por NOMBRE los sondeos contra produccion.
-/
import ROBINSON_PlusPlus
import Lean

open Lean Elab Command

def modOf' (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx =>
      let mods := env.allImportedModuleNames
      if h : idx.toNat < mods.size then mods[idx.toNat] else `UNKNOWN
  | none => `CURRENT_FILE

run_cmd do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    let m := modOf' env n
    if m.getRoot == `ROBINSON_PlusPlus || m.getRoot == `FOL then
      out := out.push s!"{n} :: {m}"
  logInfo (String.intercalate "\n" out.toList)
