/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · ¿por dónde ENTRA `Classical.choice` en los titulares?

**Fecha:** 2026‑10‑05 · **Por qué:** ADR‑129 (D7) escribió que los titulares de Gödel, la solidez y Tarski
conservan `Classical.choice` porque «su `choice` es el de la solidez clásica (`prf_sound`, el axioma `p3`)». Era
una INFERENCIA: nadie había medido de dónde sale. La auditoría del suelo (2026‑10‑05) la marcó como dudosa.

**Qué mide:** la FRONTERA de cada titular: las constantes del proyecto (`ROBINSON_PlusPlus.*`, `FOL.*`,
`TheoryFramework.*`, también las `private`) de su cierre de dependencias que nombran DIRECTAMENTE una constante
ajena cuyo cierre contiene `Classical.choice`. Es por ahí por donde entra. Sólo lee el entorno: no evalúa nada
del lenguaje objeto (ni `axioms`, ni el ancla, ni un evaluador).

* `#frontera n` — la frontera de un titular, con la constante ajena por la que entra.
* `#censoFrontera` — sobre las filas de `check-footprints.bash` de RPP que declaran `Classical.choice`: cuántas
  pasan por cada punto de entrada, y cuántas por `prf_sound`.

El resultado de la ejecución del 2026‑10‑05 está en `sondeos/README.md` (fila de este fichero) y en ADR‑131.
-/

open Lean Meta Elab Command

namespace ChoiceFrontera

/-- Nombre de usuario de una constante `private` (o el mismo nombre). -/
def nombreUsuario (n : Name) : Name := (privateToUserName? n).getD n

def esProyecto (n : Name) : Bool :=
  let m := nombreUsuario n
  (`ROBINSON_PlusPlus).isPrefixOf m || (`FOL).isPrefixOf m || (`TheoryFramework).isPrefixOf m

def directas (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some ci =>
    let ty := ci.type.getUsedConstants
    let va := ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    ty ++ va
  | none => #[]

/-- `true` si el cierre de `n` contiene `Classical.choice` (con memo; los ciclos cortan a `false`). -/
partial def tieneChoice (env : Environment) (n : Name) : StateM (Std.HashMap Name Bool) Bool := do
  if n == ``Classical.choice then return true
  if let some b := (← get).get? n then return b
  modify (·.insert n false)
  let mut r := false
  for d in directas env n do
    if ← tieneChoice env d then
      r := true
      break
  modify (·.insert n r)
  return r

partial def cierre (env : Environment) (raiz : Name) : NameSet := Id.run do
  let mut vis : NameSet := {}
  let mut pila := #[raiz]
  while h : pila.size > 0 do
    let n := pila[pila.size - 1]
    pila := pila.pop
    if vis.contains n then continue
    vis := vis.insert n
    for d in directas env n do
      if !vis.contains d then pila := pila.push d
  return vis

/-- La frontera de `raiz`: pares (constante del proyecto, constantes ajenas con `choice` que nombra). -/
def fronteraDe (env : Environment) (raiz : Name) :
    StateM (Std.HashMap Name Bool) (Array (Name × Array Name)) := do
  let mut out := #[]
  for p in (cierre env raiz).toList do
    if esProyecto p then
      let mut ajenas : Array Name := #[]
      for d in (directas env p).toList.eraseDups do
        if !esProyecto d then
          if ← tieneChoice env d then ajenas := ajenas.push d
      if ajenas.size > 0 then out := out.push (nombreUsuario p, ajenas)
  return out.qsort (fun a b => a.1.toString < b.1.toString)

elab "#frontera " id:ident : command => do
  let env ← getEnv
  let (res, _) := (fronteraDe env id.getId).run {}
  let lineas := res.toList.map fun (p, ds) => s!"  {p}  ←  {ds.toList}"
  logInfo m!"{id.getId}: {res.size} puntos de entrada\n{String.intercalate "\n" lineas}"

/-- Las filas de RPP de `check-footprints.bash` que declaran `Classical.choice`. -/
def filasConChoice : IO (Array Name) := do
  let txt ← IO.FS.readFile "check-footprints.bash"
  let mut out := #[]
  for l in txt.splitOn "\n" do
    let l := l.trimRight
    if l.startsWith "ROBINSON_PlusPlus." && (l.splitOn "|").length == 2 then
      let partes := l.splitOn "|"
      let conChoice := ((partes.getD 1 "").splitOn "Classical.choice").length > 1
      if conChoice then
        out := out.push (partes.getD 0 "").toName
  return out

elab "#censoFrontera" : command => do
  let env ← getEnv
  let filas ← filasConChoice
  let mut memo : Std.HashMap Name Bool := {}
  let mut cuenta : Std.HashMap Name Nat := {}
  let mut conSolidez := 0
  let mut soloSolidez := 0
  let mut sinSolidez := 0
  let mut ausentes := 0
  let mut soloLift := 0
  let lifts : Array Name := #[``ROBINSON_PlusPlus.Meta.SubstArith.substTerm_liftLiftLift._f,
    ``ROBINSON_PlusPlus.Meta.SubstArith.substTerm_liftLiftLiftLift._f]
  for t in filas do
    if !env.contains t then
      ausentes := ausentes + 1
      continue
    let (fr, m') := (fronteraDe env t).run memo
    memo := m'
    let ps := fr.map (·.1)
    for p in ps do cuenta := cuenta.insert p ((cuenta.getD p 0) + 1)
    let tieneSol := ps.contains ``ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound
    if tieneSol then conSolidez := conSolidez + 1 else sinSolidez := sinSolidez + 1
    if tieneSol && ps.size == 1 then soloSolidez := soloSolidez + 1
    if ps.size > 0 && ps.all (lifts.contains ·) then soloLift := soloLift + 1
  let orden := cuenta.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1.toString < b.1.toString))
  let lineas := orden.toList.map fun (p, k) => s!"  {k}  {p}"
  logInfo m!"filas con choice: {filas.size} (no encontradas en el entorno: {ausentes}) · pasan por prf_sound: {conSolidez} · sólo por prf_sound: {soloSolidez} · no pasan por prf_sound: {sinSolidez} · toda su frontera en las dos cancelaciones de lift (SubstArith.substTerm_liftLiftLift y …LiftLiftLift): {soloLift}\npuntos de entrada (filas que pasan por cada uno):\n{String.intercalate "\n" lineas}"

end ChoiceFrontera

#frontera ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf
#frontera ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf
#frontera ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound
#frontera ROBINSON_PlusPlus.Meta.Consistencia.consistencia
#frontera ROBINSON_PlusPlus.Meta.Consistencia.goedel_I
#frontera ROBINSON_PlusPlus.Meta.Consistencia.goedel_II
#frontera ROBINSON_PlusPlus.Meta.SolidezVerificador.goedel_I_neg
#frontera ROBINSON_PlusPlus.Meta.TarskiPrf.prf_tarski
#frontera ROBINSON_PlusPlus.Meta.TarskiPrf.tarski
#censoFrontera
