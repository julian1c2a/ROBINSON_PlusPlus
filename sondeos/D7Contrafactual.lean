import ROBINSON_PlusPlus

/-!
# D7, la puerta contrafactual: ¿cuántos footprints perderían `Classical.choice` sin `String`? (ADR‑122)

**Fecha**: 2026‑10‑05. Es la Etapa 0 que pidió la medición de D7 de ese día (`String` → `List Char` en FOL): antes de
pagar la migración, medir lo que compra. Viene de la sonda L5‑01 de la ronda 1 de la auditoría (escrita y nunca
ejecutada), y lee los titulares de `check-footprints.bash`.

**Cómo**: el cierre de dependencias de los titulares de RPP (tipo y valor de cada constante), y la propagación de
`Classical.choice` hacia atrás por ese grafo, dos veces: tal cual, y CORTANDO las constantes `String.*`,
`ByteArray.utf8*` y las privadas de `Init.Data.String`. Lo que sigue con `choice` tras el corte no lo limpiaría D7.

**Calibración**: «con choice hoy» tiene que coincidir con las filas de la tabla que declaran `Classical.choice` (si
`value?` no diera el valor de los teoremas importados, saldría menos).

## Medido (2026‑10‑05, RPP con ADR‑121)

    titulares: 229 · con choice hoy: 226 · con choice cortando String.*: 178

Calibra (226 = 226). **Sólo 48 de 226 perderían `Classical.choice` con D7**; 178 lo conservan por otra vía, y entre
ellos TODOS los titulares de Gödel (`goedel_first_prf`, `goedel_second_prf`, `goedel_I`, `goedel_II`, `goedel_I_neg`),
la solidez y el modelo, Tarski y `prf_diagonal`. La puerta de la medición («si la mayoría de las filas sintácticas
sale limpia, se sigue») da NO.

⚠️ Lo que NO dice: de dónde viene el `choice` de los 178 (eso pide un corte por familia de constantes), ni que D7
no tenga otro valor (simplificar `Fresh0`, las inyectividades de símbolos, la evaluación de códigos de símbolo en el
núcleo).

## Cómo re‑ejecutarlo

    lake env lean sondeos/D7Contrafactual.lean      # desde la raíz de RPP (lee check-footprints.bash)
-/

open Lean

def usedOf (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | none => #[]
  | some ci =>
    let base := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
    match ci with
    | .inductInfo iv => base ++ iv.ctors.toArray
    | _ => base

def isStr (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "String." || s.startsWith "ByteArray.utf8" || s.startsWith "_private.Init.Data.String"

def propagate (rev : Std.HashMap Name (Array Name)) (cut : Name → Bool) : NameSet := Id.run do
  let mut bad : NameSet := {}
  let mut st : Array Name := #[``Classical.choice]
  while !st.isEmpty do
    let c := st.back!
    st := st.pop
    if bad.contains c || cut c then continue
    bad := bad.insert c
    for u in rev.getD c #[] do
      unless bad.contains u do st := st.push u
  return bad

/-- Las filas `ROBINSON_PlusPlus.*` de la tabla de `check-footprints.bash`. -/
def filasRPP (lineas : Array String) : Array String := Id.run do
  let mut dentro := false
  let mut out : Array String := #[]
  for l in lineas do
    if l.startsWith "read -r -d '' TABLA <<'EOF'" then dentro := true
    else if dentro && l == "EOF" then dentro := false
    else if dentro && l.startsWith "ROBINSON_PlusPlus" then out := out.push l
  return out

#eval show CoreM Unit from do
  let env ← getEnv
  let filas := filasRPP (← IO.FS.lines "check-footprints.bash")
  let declaradas := (filas.filter fun l => (l.splitOn "Classical.choice").length > 1).size
  let tit := filas.filterMap fun l =>
    let n := ((l.splitOn "|")[0]!).toName
    if env.contains n then some n else none
  let mut seen : NameSet := {}
  let mut stack := tit
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    for d in usedOf env c do
      unless seen.contains d do stack := stack.push d
  let mut rev : Std.HashMap Name (Array Name) := {}
  for c in seen.toList do
    for d in usedOf env c do
      rev := rev.insert d ((rev.getD d #[]).push c)
  let hoy := propagate rev (fun _ => false)
  let sinStr := propagate rev isStr
  let quedan := tit.filter sinStr.contains
  IO.println s!"titulares: {tit.size} · declaran choice en la tabla: {declaradas} · con choice hoy: {(tit.filter hoy.contains).size} · con choice cortando String.*: {quedan.size}"
