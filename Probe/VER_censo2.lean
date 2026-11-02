import ROBINSON_PlusPlus.Meta

/-! Censo SIN el filtro heuristico de nombres auto-generados: solo `!isInternal`
    y «exactamente un componente tras el prefijo». Contraste con VER_censo.lean. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let root : Name := `ROBINSON_PlusPlus.Meta.CodeWitnessPrf
  for nsp in [`SinWTs, `ENS, `HW] do
    let pref := root ++ nsp
    let mut hits : Array Name := #[]
    for (n, _) in env.constants.toList do
      if pref.isPrefixOf n && !n.isInternal && n != pref then
        if (n.replacePrefix pref Name.anonymous).getNumParts == 1 then
          hits := hits.push n
    let srt := hits.qsort (fun a b => a.toString < b.toString)
    IO.println s!"### {nsp} : {srt.size}"
    for n in srt do IO.println s!"NAME {nsp} {n.getString!}"
