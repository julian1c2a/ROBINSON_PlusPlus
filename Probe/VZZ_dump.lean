import ROBINSON_PlusPlus
import Lean
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    if !n.isInternal then
      out := out.push (toString n)
  let s := String.intercalate "\n" out.toList
  IO.FS.writeFile "C:/msys64/tmp/claude/e--dropbox-github-lean4-ROBINSON-PlusPlus/85b0df6c-1e14-407d-a9ae-04b9e8841ed5/scratchpad/vzz_allnames.txt" s
  logInfo s!"total={out.size}"
