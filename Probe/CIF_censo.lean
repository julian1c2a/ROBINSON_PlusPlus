import ROBINSON_PlusPlus.Meta

/-! Censo de `env.constants` de PRODUCCION (arbol Meta completo), volcado a fichero.
    Solo lectura del entorno: no declara nada. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    if !n.isInternal then
      out := out.push n.toString
  IO.FS.writeFile
    "C:/msys64/tmp/claude/e--dropbox-github-lean4-ROBINSON-PlusPlus/85b0df6c-1e14-407d-a9ae-04b9e8841ed5/scratchpad/censo_prod.txt"
    (String.intercalate "\n" out.toList)
