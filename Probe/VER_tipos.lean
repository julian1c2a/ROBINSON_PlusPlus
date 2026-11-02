import ROBINSON_PlusPlus.Meta

/-! Censo de DUPLICADOS POR ENUNCIADO (no por nombre) dentro de `Meta/CodeWitnessPrf.lean`,
    y contra TODO el entorno. Agrupa las constantes del modulo por su TIPO (estructural)
    y reporta cada grupo con mas de un miembro. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let pref := "ROBINSON_PlusPlus.Meta.CodeWitnessPrf."
  -- 1) grupos por tipo DENTRO del modulo
  let mut byType : Std.HashMap String (Array Name) := {}
  let mut nMod := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if n.toString.startsWith pref then
      nMod := nMod + 1
      let k := toString ci.type
      byType := byType.insert k ((byType.getD k #[]).push n)
  IO.println s!"CONSTANTES DEL MODULO (no internas) = {nMod}"
  let mut nDup := 0
  for (k, v) in byType.toList do
    if v.size > 1 then
      nDup := nDup + 1
      IO.println s!"MISMO ENUNCIADO ({v.size}):"
      for n in v do IO.println s!"      {n}"
      IO.println s!"      tipo = {k.take 150}"
  IO.println s!"GRUPOS CON ENUNCIADO REPETIDO DENTRO DEL MODULO = {nDup}"

  -- 2) contra TODO el entorno: mismo tipo, constante de OTRO modulo
  let mut modTypes : Std.HashMap String Name := {}
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if n.toString.startsWith pref then
      modTypes := modTypes.insert (toString ci.type) n
  let mut nExt := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if n.toString.startsWith pref then continue
    let k := toString ci.type
    match modTypes[k]? with
    | some m =>
        nExt := nExt + 1
        if nExt ≤ 40 then IO.println s!"ENUNCIADO YA EXISTENTE FUERA: {m}  <=>  {n}"
    | none => pure ()
  IO.println s!"CONSTANTES EXTERNAS CON EL MISMO ENUNCIADO QUE ALGUNA DEL MODULO = {nExt}"
