import ROBINSON_PlusPlus.Meta

/-! Censo independiente: TODAS las declaraciones no-internas de los tres namespaces
    de `Meta/CodeWitnessPrf.lean`, para contrastar el «202 de 212» del preparador. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let root : Name := `ROBINSON_PlusPlus.Meta.CodeWitnessPrf
  for nsp in [`SinWTs, `ENS, `HW] do
    let pref := root ++ nsp
    let mut hits : Array Name := #[]
    for (n, ci) in env.constants.toList do
      if pref.isPrefixOf n && !n.isInternal && n != pref then
        -- descartar los auto-generados del compilador
        let s := n.toString
        let auto := [".eq_", ".match_", ".proof_", ".rec", ".casesOn", ".below", ".brecOn",
                     ".ind", ".noConfusion", ".sizeOf", ".injEq", ".ctorIdx", ".eq_def",
                     "._unary", ".induct", ".fun_cases", ".eq_unfold", ".def"]
        let isAuto := auto.any (fun a => (s.splitOn a).length > 1)
        if !isAuto && !ci.isUnsafe then
          -- solo el ultimo componente, sin sub-namespaces
          if (n.replacePrefix pref Name.anonymous).getNumParts == 1 then
            hits := hits.push n
    let srt := hits.qsort (fun a b => a.toString < b.toString)
    IO.println s!"### {nsp} : {srt.size}"
    for n in srt do
      IO.println s!"NAME {nsp} {n.getString!}"
