/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.PurezaComando
import ROBINSON_PlusPlus.Meta.Consistencia
import ROBINSON_PlusPlus.Meta.TarskiPrf
import ROBINSON_PlusPlus.Meta.Rosser
import ROBINSON_PlusPlus.Meta.Lob
import ROBINSON_PlusPlus.Meta.GodelCorolarios
import ROBINSON_PlusPlus.Meta.RigidezEstandar

/-!
# `Meta/ContratoTitulares.lean` — T07: el CONTRATO de los enunciados de los titulares (ADR‑165)

**Por qué.** `check-footprints.bash` compara la lista de axiomas de cada titular, y T08 que su cierre no nombre la
semántica. Ninguno fija el ENUNCIADO. Un cambio coherente que debilitara un titular, o que cambiara `godelCN` por otra
sentencia, pasaba todos los controles (T07 de la auditoría). Un `example : ¬ Prf godelCN := goedel_I` tampoco basta:
fija el tipo por NOMBRE, y redefinir `godelCN`, `Prf` o `axioms` no lo rompe.

**Qué fija.** Para cada titular de `TITULARES` (los 29 de `T_UNIVERSO`, que `check-doc-sync.bash` [T] compara con esta
lista), el CIERRE de su tipo: las constantes del proyecto que alcanza el enunciado. El cierre sigue el tipo de cada
una, el VALOR de las definiciones, los constructores de los inductivos y el inductivo de los constructores, y no entra
en la prueba de ningún teorema. De cada constante guarda una huella: `Expr.hash` de su tipo y, si es una definición,
de su valor; de un inductivo, también la lista de sus constructores. La tabla está en `Meta/ContratoTabla.lean`, la
escribe `#contrato_generar` (`scripts/ContratoGenerar.lean`), y `#contrato_titulares` (`Meta/PurezaTitulares.lean`)
rompe el build si no coincide en los dos sentidos: una huella distinta, una constante nueva en el cierre o una que ya
no está. La tabla sólo cambia con un ADR.

**Lo que NO fija.** Las pruebas: un teorema del cierre aporta sólo su tipo. Lo de Lean (`Nat`, `List`, `Eq`…), que es
la base confiada y cambia con el toolchain, que lleva su ADR. Un cambio en el término elaborado de una definición que
no cambie su sentido (otra táctica de terminación, por ejemplo) también cambia su huella: se revisa y se regenera con
su ADR. La huella del tipo es de 32 bits (`Expr.hash`), y un cambio puede pasar inadvertido con probabilidad 2⁻³².
Y no habría cazado F1: el `[AnclaEq]` estaba en el enunciado publicado, y la tabla lo habría fijado.

Este módulo no comprueba nada: da la lista, el recorrido y el generador. No importa la tabla, para que el generador
funcione también cuando la tabla está desfasada.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Lean Elab Command

namespace ROBINSON_PlusPlus.Meta.ContratoTitulares

open ROBINSON_PlusPlus.Meta.PurezaComando (delProyecto nombreUsuario)

/-- Los 29 titulares de `T_UNIVERSO` (`check-doc-sync.bash` [T], `TEOREMAS-E-HIPOTESIS.md` §1). Añadir o quitar uno
    pide su ADR, su fila en TEOREMAS, su nombre en `T_UNIVERSO` y regenerar la tabla. -/
def TITULARES : List Name := [
  ``ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf,
  ``ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf,
  ``ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_con_imp_godel,
  ``ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_godelCN_fixedpoint,
  ``ROBINSON_PlusPlus.Meta.TarskiPrf.prf_tarski,
  ``ROBINSON_PlusPlus.Meta.Consistencia.goedel_I,
  ``ROBINSON_PlusPlus.Meta.Consistencia.goedel_II,
  ``ROBINSON_PlusPlus.Meta.TarskiPrf.tarski,
  ``ROBINSON_PlusPlus.Meta.SolidezVerificador.goedel_I_neg,
  ``ROBINSON_PlusPlus.Meta.SolidezVerificador.godelCN_indecidible,
  ``ROBINSON_PlusPlus.Meta.SolidezVerificador.modelo_prov_iff,
  ``ROBINSON_PlusPlus.Meta.SolidezVerificador.godelCN_verdadera,
  ``ROBINSON_PlusPlus.Meta.SolidezVerificador.con_verdadera,
  ``ROBINSON_PlusPlus.Meta.TarskiPrf.tarski_semantico,
  ``ROBINSON_PlusPlus.Meta.Consistencia.consistencia,
  ``ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf,
  ``ROBINSON_PlusPlus.Meta.DerivCondPrf.d2_prf,
  ``ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real,
  ``ROBINSON_PlusPlus.Meta.Rosser.rosser_ext,
  ``ROBINSON_PlusPlus.Meta.Rosser.rosser,
  ``ROBINSON_PlusPlus.Meta.Lob.lob,
  ``ROBINSON_PlusPlus.Meta.GodelCorolarios.prf_godel_iff_con,
  ``ROBINSON_PlusPlus.Meta.GodelCorolarios.goedel_second_formalizado,
  ``ROBINSON_PlusPlus.Meta.GodelCorolarios.con_indecidible,
  -- ✏️ 2026‑10‑20 (ADR‑174): los cuatro de T75e, titulares por decisión del propietario.
  ``ROBINSON_PlusPlus.Meta.RigidezEstandar.prf_of_prov_de,
  ``ROBINSON_PlusPlus.Meta.RigidezEstandar.modelo_prov_iff_de,
  ``ROBINSON_PlusPlus.Meta.RigidezEstandar.godelCN_verdadera_de,
  ``ROBINSON_PlusPlus.Meta.RigidezEstandar.con_verdadera_de,
  -- ✏️ 2026‑10‑21 (ADR‑178): `tarski_semantico_de` (T75a), titular por decisión del propietario.
  ``ROBINSON_PlusPlus.Meta.TarskiPrf.tarski_semantico_de]

/-- Las constantes de una expresión, también las estructuras de sus proyecciones (`Expr.proj`), que
    `getUsedConstants` no ve. -/
def constantesDe (e : Expr) : Array Name := Id.run do
  let mut out := e.getUsedConstants
  let mut vistas : NameSet := {}
  repeat
    match e.find? (fun x => match x with | .proj s _ _ => !vistas.contains s | _ => false) with
    | some (.proj s _ _) =>
      vistas := vistas.insert s
      out := out.push s
    | _ => break
  return out

/-- Las aristas del cierre de un ENUNCIADO: el tipo de cada constante; el valor de las definiciones; los constructores
    de un inductivo, el inductivo de un constructor y los de un recursor. De un teorema, sólo el tipo. -/
def aristas (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let s := constantesDe ci.type
    match ci with
    | .defnInfo v => s ++ constantesDe v.value
    | .opaqueInfo v => s ++ constantesDe v.value
    | .inductInfo v => s ++ v.ctors.toArray
    | .ctorInfo v => s.push v.induct
    | .recInfo v => s ++ v.all.toArray
    | _ => s

/-- La huella: `Expr.hash` del tipo; con el del valor, en una definición; con la lista de constructores, en un
    inductivo. -/
def huella (ci : ConstantInfo) : UInt64 :=
  let t := ci.type.hash
  match ci with
  | .defnInfo v => mixHash t v.value.hash
  | .opaqueInfo v => mixHash t v.value.hash
  | .inductInfo v => mixHash t (hash v.ctors)
  | _ => t

def clase (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .inductInfo _ => "ind"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"

/-- El cierre del TIPO de `t`: `t` (por su tipo) y lo que alcanza, sólo por constantes del proyecto. -/
def cierreTipo (env : Environment) (t : Name) : Array Name := Id.run do
  let mut vistos : NameSet := ({} : NameSet).insert t
  let mut cola : Array Name := #[t]
  let mut i := 0
  while i < cola.size do
    let n := cola[i]!
    i := i + 1
    let ds := if n == t then (match env.find? t with | some ci => constantesDe ci.type | none => #[]) else aristas env n
    for d in ds do
      if !vistos.contains d && delProyecto env d then
        vistos := vistos.insert d
        cola := cola.push d
  return cola

/-- Una línea de la tabla: clase, huella y nombre. -/
structure Entrada where
  clase : String
  huella : String
  nombre : String
deriving BEq

/-- El contrato calculado: las entradas (ordenadas por nombre) y, para cada nombre, los titulares que lo alcanzan. -/
def calcular (env : Environment) (titulares : List Name) : Array Entrada × Std.HashMap String (Array Name) := Id.run do
  let mut quien : Std.HashMap String (Array Name) := {}
  let mut entradas : Std.HashMap String Entrada := {}
  for t in titulares do
    for n in cierreTipo env t do
      let some ci := env.find? n | continue
      let k := toString n
      quien := quien.insert k ((quien.getD k #[]).push t)
      entradas := entradas.insert k { clase := clase ci, huella := toString (huella ci), nombre := k }
  let arr := entradas.toArray.map (·.2) |>.qsort (fun a b => a.nombre < b.nombre)
  return (arr, quien)

def lineaDe (e : Entrada) : String := s!"{e.clase} {e.huella} {e.nombre}"

/-- Lee la tabla: una entrada por línea no vacía (`clase huella nombre`). -/
def leerTabla (s : String) : Std.HashMap String Entrada := Id.run do
  let mut m : Std.HashMap String Entrada := {}
  for l in s.splitOn "\n" do
    match (l.trimAscii.toString.splitOn " ") with
    | [c, h, n] => m := m.insert n { clase := c, huella := h, nombre := n }
    | _ => pure ()
  return m

/-- El control: el contrato calculado tiene que ser EXACTAMENTE la tabla. Además, `PUROS` e `IMPUROS` (T08) son
    titulares. -/
def comprobar (titulares : List Name) (tabla : String) (puros impuros : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut fallos : Array String := #[]
  for t in titulares do
    unless env.contains t do fallos := fallos.push s!"el titular {t} NO EXISTE (¿renombrado?)"
  for t in puros ++ impuros do
    unless titulares.contains t do fallos := fallos.push s!"{t} está en PUROS o IMPUROS (T08) y NO en TITULARES"
  let (cal, quien) := calcular env titulares
  let tab := leerTabla tabla
  let usan (k : String) : String :=
    ", ".intercalate ((quien.getD k #[]).toList.map (fun t => toString (nombreUsuario t).getString!))
  let mut nCambian := 0
  for e in cal do
    match tab.get? e.nombre with
    | none =>
      fallos := fallos.push s!"NUEVA en el cierre: {e.clase} {e.nombre} (la alcanzan: {usan e.nombre})"
    | some f =>
      unless f == e do
        nCambian := nCambian + 1
        fallos := fallos.push s!"CAMBIA: {e.clase} {e.nombre}: la tabla dice {f.clase} {f.huella}, hoy es {e.huella} (la alcanzan: {usan e.nombre})"
  let enCalc : Std.HashSet String := cal.foldl (fun s e => s.insert e.nombre) {}
  for (k, f) in tab.toList do
    unless enCalc.contains k do fallos := fallos.push s!"YA NO ESTÁ en el cierre: {f.clase} {k}"
  let porClase := cal.foldl (fun (m : Std.HashMap String Nat) e => m.insert e.clase (m.getD e.clase 0 + 1)) {}
  let resumen := ", ".intercalate (["def", "ind", "ctor", "rec", "thm", "opaque", "axiom", "quot"].filterMap
    (fun c => match porClase.get? c with | some k => some s!"{k} {c}" | none => none))
  if fallos.isEmpty then
    logInfo m!"T07 · contrato de los enunciados (ADR‑165): {titulares.length} titulares; {cal.size} constantes del proyecto en el cierre de sus tipos ({resumen}), todas con la huella de la tabla"
  else
    let muestra := (fallos.toList.take 60)
    let resto := if fallos.size > 60 then s!"\n  … y {fallos.size - 60} más" else ""
    throwError m!"⛔ T07 · el contrato de los enunciados FALLA (ADR‑165): {fallos.size} diferencias con la tabla\n  {"\n  ".intercalate muestra}{resto}\n  Si el cambio es querido: su ADR, y `lake env lean scripts/ContratoGenerar.lean` regenera Meta/ContratoTabla.lean."

/-- El fichero de la tabla, generado. -/
def ficheroTabla (titulares : List Name) (cal : Array Entrada) : String :=
  let cuerpo := "\n".intercalate (cal.toList.map lineaDe)
  "/-\nCopyright (c) 2026. All rights reserved.\nAuthor: Julián Calderón Almendros\nLicense: MIT\n-/\n\n" ++
  "/-!\n# `Meta/ContratoTabla.lean` — la TABLA del contrato de los enunciados de los titulares (T07, ADR‑165)\n\n" ++
  "⛔ GENERADO por `lake env lean scripts/ContratoGenerar.lean`, que lee `TITULARES` de `Meta/ContratoTitulares.lean`:\n" ++
  "no se edita a mano, y sólo cambia con un ADR. Una línea por constante del cierre de los tipos de los titulares: su\n" ++
  "clase, su huella y su nombre. La comprueba `#contrato_titulares`, en `Meta/PurezaTitulares.lean`.\n-/\n\n" ++
  "namespace ROBINSON_PlusPlus.Meta.ContratoTabla\n\n" ++
  s!"/-- {cal.size} constantes del cierre de los tipos de {titulares.length} titulares. -/\n" ++
  "def tabla : String := \"\n" ++ cuerpo ++ "\n\"\n\nend ROBINSON_PlusPlus.Meta.ContratoTabla\n"

/-- `#contrato_generar "ruta"`: escribe la tabla de `TITULARES` en `ruta` (desde la raíz de RPP). -/
syntax (name := contratoGenerar) "#contrato_generar " str : command

@[command_elab contratoGenerar] def elabContratoGenerar : CommandElab := fun stx => do
  let some ruta := stx[1].isStrLit? | throwError "#contrato_generar: falta la ruta"
  let (cal, _) := calcular (← getEnv) TITULARES
  if cal.any (fun e => e.nombre.any (fun c => c == '"' || c == '\\')) then
    throwError "#contrato_generar: un nombre lleva comillas o barras; la tabla no sabe escribirlo"
  IO.FS.writeFile ruta (ficheroTabla TITULARES cal)
  logInfo m!"T07 · tabla del contrato escrita en {ruta}: {cal.size} constantes de {TITULARES.length} titulares"

end ROBINSON_PlusPlus.Meta.ContratoTitulares
