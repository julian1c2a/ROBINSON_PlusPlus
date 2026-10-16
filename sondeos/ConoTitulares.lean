/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · el CONO de los titulares, por DECLARACIÓN

**Fecha:** 2026‑10‑16 · **Por qué:** ADR‑139 (el plan para acotar el proyecto). El 2026‑10‑16 se midió el cono a nivel
de MÓDULO (los `import`): los 18 titulares arrastran 105 de los 113 ficheros del build y 12 de FOL. Por módulo el cono
sale MÁS GRANDE de lo que es: un módulo importado por un solo lema cuenta entero. Esto lo mide por declaración.

**Qué mide.** El cierre de dependencias de los 18 titulares de `T_UNIVERSO` (`check-doc-sync.bash`), sólo por
constantes de RPP y de FOL: las del TIPO y del VALOR de cada una (`allowOpaque`), las estructuras de las proyecciones
(`Expr.proj`, que `getUsedConstants` no ve), y de un inductivo sus constructores (y al revés). Cada constante se asigna
a su DECLARACIÓN del fuente: la suya si tiene rango (`findDeclarationRanges?`), si no la de su prefijo
(`foo.proof_1`, `foo.match_1`, `foo.eq_1` → `foo`). Una declaración del fuente es un rango MAXIMAL de un módulo (los
constructores y los campos quedan dentro del de su tipo).

**Ámbito (M‑13).** Es el cono del NÚCLEO: lo que el kernel necesita para comprobar los enunciados y las pruebas de los
titulares tal como quedaron elaborados. Fuera del cono no quiere decir «se puede borrar sin tocar nada»: una táctica,
una notación o un `simp [foo]` cuyo lema no acabó en el término se necesitan para ELABORAR el fuente y el kernel no los
ve. Por eso las declaraciones de ELABORACIÓN (las que devuelven algo de `Lean.*` o de `IO`: sintaxis, macros,
tácticas) se cuentan aparte, y las líneas fuera de toda declaración (comentarios, docstrings de módulo, `example`,
`#print`, `open`, líneas en blanco) también.

**Escribe** (efecto lateral; la ruta es relativa a la raíz de RPP): `doc/registro/2026-10-16-cono/resumen.txt`,
`por-modulo.csv` y `fuera-del-cono.txt`. Se lanza con `lake env lean sondeos/ConoTitulares.lean` desde la raíz.

**Controles** (dentro de `#cono`, antes de escribir nada; si uno falla, no se escribe): (1) el cono de la clase (i) de
ADR‑135 no nombra `SolidezPrf` y el de `consistencia` sí, como mide `#modelo` (`sondeos/InduccionTitulares.lean`);
(2) ninguna declaración de un módulo fuera del cono de imports (`Meta/VerifierSound.lean`) queda dentro; (3) cada
titular cae en su propia declaración, y dentro; (4) las constantes del cono sin declaración a la que asignarlas se
cuentan y se listan. La primera versión asignaba un auxiliar a una línea de SU módulo, y un auxiliar puede generarse
en otro (las ecuaciones de `ModeloCodigo.stepT.match_1` viven en `ModeloCodificacion`): dejaba 39 sin dueño y podía
marcar una declaración ajena que cayera en esa línea. Hoy va por el nombre de usuario (`indiceRangos`).

**Resultado de la ejecución del 2026‑10‑16** (80 s; la salida entera, en `doc/registro/2026-10-16-cono/`). Los
controles pasan; sin dueño quedan 3 auxiliares `_arg_pusher` de `PSum`/`PSigma` (de Lean, generados en
`SolidezVerificador` y `ModeloCodigo`).
* RPP, los 112 módulos del build con sus dos barriles: 52.634 líneas, 34.622 dentro de una declaración y 18.012 fuera
  de toda declaración. De 3.623 declaraciones, 2.847 (79 %) están en el cono, con 28.578 líneas; fuera quedan 776, con
  6.044.
* FOL: RPP importa 12 de sus 163 ficheros (2.840 líneas); 4 aportan algo al cono: 48 de 193 declaraciones, 481 líneas.
* 21 ficheros importados no aportan nada al cono: los dos barriles; `Minimal/SymLit` (la macro `sym!`, elaboración
  pura); `Full/PrimeFactor`; nueve de `Meta/` (`ChainDecode`, `ChainNegPrf`, `CodeDecode`, `CodeDistinct`,
  `OmegaReflect`, `ReflectionPrf`, `Sigma1BoundedPrf`, `Sigma1TrackedPrf`, `VerifierSound`); y ocho de FOL. Por
  módulo se veían ocho de RPP fuera; `CodeDistinct`, `ReflectionPrf`, `Sigma1TrackedPrf` y `SymLit` se importan, pero
  el núcleo no usa nada suyo.
* Por titular: D3 (`d3_prf_real`) arrastra 2.444 declaraciones y 26.880 líneas, el 92 % del cono; Gödel I condicional
  (`goedel_first_prf`), 720 y 5.164; la clase (i) entera, 2.478 y 27.158; lo que sólo piden `consistencia` y las
  clases (ii) y (iii), 417 y 1.901.
-/

open Lean Meta Elab Command

namespace ConoTitulares

def nombreUsuario (n : Name) : Name := (privateToUserName? n).getD n

def esModProyecto (m : Name) : Bool :=
  (`ROBINSON_PlusPlus).isPrefixOf m || (`FOL).isPrefixOf m || (`TheoryFramework).isPrefixOf m

def moduloDe (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  env.header.moduleNames[i.toNat]?

def delProyecto (env : Environment) (n : Name) : Bool :=
  match moduloDe env n with
  | some m => esModProyecto m
  | none => false

/-- Las constantes y las estructuras de las proyecciones de `e`, recorriendo el GRAFO con memoria (los términos de
    prueba comparten mucho: recorrerlos como árbol no acaba; ver `sondeos/InduccionTitulares.lean`). -/
unsafe def usadosImpl (e : Expr) : Array Name := Id.run do
  let mut vis : PtrSet Expr := mkPtrSet
  let mut pila : Array Expr := #[e]
  let mut out : NameSet := {}
  while h : pila.size > 0 do
    let x := pila[pila.size - 1]
    pila := pila.pop
    if vis.contains x then continue
    vis := vis.insert x
    match x with
    | .const n _ => out := out.insert n
    | .proj s _ b => out := out.insert s; pila := pila.push b
    | .app f a => pila := (pila.push f).push a
    | .lam _ t b _ => pila := (pila.push t).push b
    | .forallE _ t b _ => pila := (pila.push t).push b
    | .letE _ t v b _ => pila := ((pila.push t).push v).push b
    | .mdata _ b => pila := pila.push b
    | _ => pure ()
  return out.toList.toArray

@[implemented_by usadosImpl] opaque usados (e : Expr) : Array Name

def directas (env : Environment) (n : Name) : Array Name := Id.run do
  let some ci := env.find? n | return #[]
  let mut s := usados ci.type
  if let some v := ci.value? (allowOpaque := true) then s := s ++ usados v
  match ci with
  | .inductInfo v => s := s ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => s := s.push v.induct
  | .recInfo v => s := s ++ v.all.toArray
  | _ => pure ()
  return s

/-- El cierre de `raices`, sólo por constantes de RPP y de FOL (lo de Lean no puede nombrar nada del proyecto). -/
partial def cierre (env : Environment) (raices : List Name) : NameSet := Id.run do
  let mut vis : NameSet := {}
  let mut pila : Array Name := raices.toArray
  while h : pila.size > 0 do
    let n := pila[pila.size - 1]
    pila := pila.pop
    if vis.contains n then continue
    vis := vis.insert n
    for d in directas env n do
      if !vis.contains d && delProyecto env d then pila := pila.push d
  return vis

/-- Los 18 de `T_UNIVERSO`, con la clase de ADR‑135 (`TEOREMAS-E-HIPOTESIS.md` §1; «—» para `consistencia`). -/
def titulares : List (Name × String) := [
  (``ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf, "i"),
  (``ROBINSON_PlusPlus.Meta.DerivCondPrf.d2_prf, "i"),
  (``ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real, "i"),
  (``ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_godelCN_fixedpoint, "i"),
  (``ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_con_imp_godel, "i"),
  (``ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf, "i"),
  (``ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf, "i"),
  (``ROBINSON_PlusPlus.Meta.TarskiPrf.prf_tarski, "i"),
  (``ROBINSON_PlusPlus.Meta.Consistencia.consistencia, "—"),
  (``ROBINSON_PlusPlus.Meta.Consistencia.goedel_I, "ii"),
  (``ROBINSON_PlusPlus.Meta.Consistencia.goedel_II, "ii"),
  (``ROBINSON_PlusPlus.Meta.TarskiPrf.tarski, "ii"),
  (``ROBINSON_PlusPlus.Meta.SolidezVerificador.goedel_I_neg, "iii"),
  (``ROBINSON_PlusPlus.Meta.SolidezVerificador.godelCN_indecidible, "iii"),
  (``ROBINSON_PlusPlus.Meta.SolidezVerificador.godelCN_verdadera, "iii"),
  (``ROBINSON_PlusPlus.Meta.SolidezVerificador.con_verdadera, "iii"),
  (``ROBINSON_PlusPlus.Meta.SolidezVerificador.modelo_prov_iff, "iii"),
  (``ROBINSON_PlusPlus.Meta.TarskiPrf.tarski_semantico, "iii")]

/-- ¿Es de ELABORACIÓN? Su tipo, quitados los `∀`, tiene la cabeza en `Lean.*` o en `IO`: sintaxis, macros,
    tácticas, elaboradores. -/
def esMeta (ci : ConstantInfo) : Bool :=
  let rec cuerpo : Expr → Expr
    | .forallE _ _ b _ => cuerpo b
    | e => e
  match (cuerpo ci.type).getAppFn with
  | .const n _ => [`Lean, `IO, `EIO, `BaseIO].contains n.getRoot
  | _ => false

/-- Una declaración del fuente: un rango MAXIMAL de un módulo. -/
structure Decl where
  modulo : Name
  ini : Nat
  fin : Nat
  nombre : Name
  esElab : Bool
  deriving Inhabited

def capa (m : Name) : String :=
  if (`ROBINSON_PlusPlus.Minimal).isPrefixOf m then "RPP/Minimal"
  else if (`ROBINSON_PlusPlus.Full).isPrefixOf m then "RPP/Full"
  else if (`ROBINSON_PlusPlus.Meta).isPrefixOf m then "RPP/Meta"
  else if (`ROBINSON_PlusPlus).isPrefixOf m then "RPP/raíz"
  else if (`FOL).isPrefixOf m then "FOL"
  else "TheoryFramework"

/-- Nombre de USUARIO ↦ (módulo, línea de inicio) de cada constante del proyecto con rango propio. Va por el nombre de
    usuario porque un auxiliar puede generarse en OTRO módulo y con otro prefijo privado que su dueño (medido: las
    ecuaciones de `ModeloCodigo.stepT.match_1` viven en `ModeloCodificacion`). -/
def indiceRangos : CommandElabM (Std.HashMap Name (Array (Name × Nat))) := do
  let env ← getEnv
  let mut out : Std.HashMap Name (Array (Name × Nat)) := {}
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless esModProyecto m do continue
    for c in env.header.moduleData[i]!.constNames do
      if let some r ← findDeclarationRangesCore? c then
        let u := nombreUsuario c
        out := out.insert u ((out.getD u #[]).push (m, r.range.pos.line))
  return out

/-- La declaración (módulo, línea) a la que pertenece `n`: la suya, o la de su prefijo más largo que tenga rango; entre
    homónimos privados de módulos distintos, la del módulo de `n`. -/
def dueno (env : Environment) (idx : Std.HashMap Name (Array (Name × Nat))) (n : Name) : Option (Name × Nat) := Id.run do
  let propio := moduloDe env n
  let mut m := nombreUsuario n
  for _ in [0:8] do
    if m.isAnonymous then return none
    if let some cs := idx.get? m then
      if let some p := cs.find? (fun p => some p.1 == propio) then return some p
      if h : cs.size > 0 then return some cs[0]
    m := m.getPrefix
  return none

/-- Todo lo que el sondeo necesita, calculado una vez. -/
structure Medida where
  decls : Std.HashMap Name (Array Decl)          -- por módulo, ordenadas por línea
  enCono : Std.HashMap Name (Array Bool)
  conoTotal : NameSet
  sinDueno : Array Name
  lineasFich : Std.HashMap Name Nat
  idx : Std.HashMap Name (Array (Name × Nat))

def buscar (ds : Array Decl) (l : Nat) : Option Nat := Id.run do
  for i in [0:ds.size] do
    if ds[i]!.ini ≤ l && l ≤ ds[i]!.fin then return some i
  return none

/-- Las declaraciones MAXIMALES de cada módulo del proyecto. -/
def declaraciones : CommandElabM (Std.HashMap Name (Array Decl)) := do
  let env ← getEnv
  let mut out : Std.HashMap Name (Array Decl) := {}
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless esModProyecto m do continue
    let mut rs : Array (Nat × Nat × Name × Bool) := #[]
    for c in env.header.moduleData[i]!.constNames do
      if let some r ← findDeclarationRangesCore? c then
        let el := match env.find? c with | some ci => esMeta ci | none => false
        rs := rs.push (r.range.pos.line, r.range.endPos.line, c, el)
    -- maximales: por inicio creciente y fin decreciente; uno contenido en el anterior maximal no lo es
    let ord := rs.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 > b.2.1))
    let mut ds : Array Decl := #[]
    for (a, b, c, mt) in ord do
      if h : ds.size > 0 then
        let u := ds[ds.size - 1]
        if a ≥ u.ini && b ≤ u.fin then
          -- dentro: si el de dentro NO es de elaboración, la declaración tampoco
          if !mt && u.esElab then ds := ds.set! (ds.size - 1) { u with esElab := false }
          continue
      ds := ds.push { modulo := m, ini := a, fin := b, nombre := c, esElab := mt }
    out := out.insert m ds
  return out

def lineasDe (m : Name) : IO Nat := do
  let sp ← getSrcSearchPath
  match ← sp.findWithExt "lean" m with
  | some p =>
    -- como `wc -l`: los saltos de línea
    let s ← IO.FS.readFile p
    return s.foldl (fun n c => if c == '\n' then n + 1 else n) 0
  | none => return 0

/-- Marca las declaraciones que contienen alguna constante de `cono`; devuelve también las que no tienen dueño. -/
def marcar (decls : Std.HashMap Name (Array Decl)) (idx : Std.HashMap Name (Array (Name × Nat))) (cono : NameSet) :
    CommandElabM (Std.HashMap Name (Array Bool) × Array Name) := do
  let env ← getEnv
  let mut marca : Std.HashMap Name (Array Bool) := {}
  for (m, ds) in decls.toList do marca := marca.insert m (Array.replicate ds.size false)
  let mut sin : Array Name := #[]
  for c in cono.toList do
    let some (m, l) := dueno env idx c | sin := sin.push c; continue
    match buscar (decls.getD m #[]) l with
    | some i => marca := marca.insert m ((marca.getD m #[]).set! i true)
    | none => sin := sin.push c
  return (marca, sin)

def medir : CommandElabM Medida := do
  let env ← getEnv
  let decls ← declaraciones
  let cono := cierre env (titulares.map (·.1))
  let idx ← indiceRangos
  let (marca, sin) ← marcar decls idx cono
  let mut lin : Std.HashMap Name Nat := {}
  for (m, _) in decls.toList do lin := lin.insert m (← lineasDe m)
  return { decls, enCono := marca, conoTotal := cono, sinDueno := sin, lineasFich := lin, idx }

def lineasDecl (d : Decl) : Nat := d.fin + 1 - d.ini

/-- (declaraciones, de elaboración, en el cono, líneas en declaraciones, líneas en el cono) de una lista de módulos. -/
def cuentas (md : Medida) (ms : List Name) : Nat × Nat × Nat × Nat × Nat := Id.run do
  let mut (n, nm, nc, l, lc) := (0, 0, 0, 0, 0)
  for m in ms do
    let ds := md.decls.getD m #[]
    let mk := md.enCono.getD m #[]
    for i in [0:ds.size] do
      let d := ds[i]!
      n := n + 1; l := l + lineasDecl d
      if d.esElab then nm := nm + 1
      if mk[i]! then nc := nc + 1; lc := lc + lineasDecl d
  return (n, nm, nc, l, lc)

def pct (a b : Nat) : String := if b == 0 then "—" else s!"{(a * 1000 / b + 5) / 10} %"

/-- Declaraciones del cono de `raices` (cuántas y cuántas líneas), sobre `md`. -/
def tamCono (md : Medida) (raices : List Name) : CommandElabM (Nat × Nat) := do
  let env ← getEnv
  let (marca, _) ← marcar md.decls md.idx (cierre env raices)
  let mut (n, l) := (0, 0)
  for (m, ds) in md.decls.toList do
    let mk := marca.getD m #[]
    for i in [0:ds.size] do
      if mk[i]! then n := n + 1; l := l + lineasDecl ds[i]!
  return (n, l)

/-- Los controles: si alguno falla, la medida no vale y no se escribe nada. -/
def controles (md : Medida) : CommandElabM (Bool × String) := do
  let env ← getEnv
  let sol := `ROBINSON_PlusPlus.Meta.SolidezPrf
  -- (1) la clase (i) no nombra `SolidezPrf`; `consistencia`, sí (lo que mide `#modelo`)
  let ci := cierre env (titulares.filter (·.2 == "i") |>.map (·.1))
  let cc := cierre env [``ROBINSON_PlusPlus.Meta.Consistencia.consistencia]
  let c1a := !(ci.toList.any (fun n => sol.isPrefixOf (nombreUsuario n)))
  let c1b := cc.toList.any (fun n => sol.isPrefixOf (nombreUsuario n))
  -- (2) nada de `Meta/VerifierSound.lean`, fuera del cono de imports, dentro del cono
  let vs := `ROBINSON_PlusPlus.Meta.VerifierSound
  let mk := md.enCono.getD vs #[]
  let c2 := mk.size > 0 && !(mk.any id)
  -- (3) cada titular, dentro del cono y en su propia declaración
  let mut c3 := true
  for (t, _) in titulares do
    let some m := moduloDe env t | c3 := false; continue
    let some r ← findDeclarationRanges? t | c3 := false; continue
    match buscar (md.decls.getD m #[]) r.range.pos.line with
    | some i => if !((md.enCono.getD m #[])[i]!) then c3 := false
    | none => c3 := false
  let txt := s!"controles:
  (1a) la clase (i) no nombra SolidezPrf: {c1a}
  (1b) consistencia sí la nombra: {c1b}
  (2) nada de Meta/VerifierSound en el cono ({mk.size} declaraciones allí): {c2}
  (3) cada titular está en el cono, en su declaración: {c3}
  (4) constantes del cono sin declaración a la que asignarlas: {md.sinDueno.size} {md.sinDueno.toList.map toString}
"
  return (c1a && c1b && c2 && c3, txt)

elab "#cono" : command => do
  let md ← medir
  let (ok, txtC) ← controles md
  unless ok do throwError "un control del cono FALLA: la medida no vale\n{txtC}"
  let dir : System.FilePath := "doc/registro/2026-10-16-cono"
  IO.FS.createDirAll dir
  let mods := md.decls.toList.map (·.1) |>.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
  -- por módulo
  let mut csv := "modulo,capa,lineas_fichero,declaraciones,de_elaboracion,en_el_cono,lineas_en_declaraciones,lineas_en_el_cono\n"
  for m in mods do
    let (n, nm, nc, l, lc) := cuentas md [m]
    csv := csv ++ s!"{m},{capa m},{md.lineasFich.getD m 0},{n},{nm},{nc},{l},{lc}\n"
  IO.FS.writeFile (dir / "por-modulo.csv") csv
  -- fuera del cono, declaración a declaración
  let mut fuera := "# Declaraciones FUERA del cono del núcleo de los 18 titulares (2026-10-16, sondeos/ConoTitulares.lean).\n# módulo:inicio-fin (líneas) nombre [E = de elaboración]\n"
  for m in mods do
    let ds := md.decls.getD m #[]
    let mk := md.enCono.getD m #[]
    for i in [0:ds.size] do
      unless mk[i]! do
        let d := ds[i]!
        fuera := fuera ++ s!"{m}:{d.ini}-{d.fin} ({lineasDecl d}) {nombreUsuario d.nombre}{if d.esElab then " [E]" else ""}\n"
  IO.FS.writeFile (dir / "fuera-del-cono.txt") fuera
  -- resumen por capa
  let capas := ["RPP/Minimal", "RPP/Full", "RPP/Meta", "RPP/raíz", "FOL", "TheoryFramework"]
  let mut res := "CONO DEL NÚCLEO de los 18 titulares de T_UNIVERSO, por DECLARACIÓN — 2026-10-16, sondeos/ConoTitulares.lean\n"
  res := res ++ "(ámbito: lo que el kernel necesita para comprobar los titulares; ver la cabecera del sondeo)\n"
  res := res ++ s!"constantes del proyecto en el cono: {md.conoTotal.size}\n\n"
  res := res ++ "capa | módulos importados | con algo en el cono | líneas de los ficheros | líneas fuera de toda declaración | declaraciones | de elaboración | en el cono | líneas en declaraciones | líneas en el cono\n"
  for k in capas do
    let ms := mods.filter (capa · == k)
    if ms.isEmpty then continue
    let (n, nm, nc, l, lc) := cuentas md ms
    let conAlgo := ms.filter (fun m => (md.enCono.getD m #[]).any id) |>.length
    let lf := ms.foldl (fun a m => a + md.lineasFich.getD m 0) 0
    res := res ++ s!"{k} | {ms.length} | {conAlgo} | {lf} | {lf - l} | {n} | {nm} | {nc} ({pct nc n}) | {l} | {lc} ({pct lc lf} de las del fichero)\n"
  let vacios := mods.filter (fun m => !((md.enCono.getD m #[]).any id))
  res := res ++ s!"\nmódulos importados SIN NADA en el cono ({vacios.length}): {vacios.map toString}\n"
  -- por titular, y la clase (i) frente al total
  res := res ++ "\ntitular | clase | declaraciones en su cono | líneas\n"
  for (t, c) in titulares do
    let (n, l) ← tamCono md [t]
    res := res ++ s!"{t} | {c} | {n} | {l}\n"
  let (ni, li) ← tamCono md (titulares.filter (·.2 == "i") |>.map (·.1))
  let (nt, lt) ← tamCono md (titulares.map (·.1))
  res := res ++ s!"\nclase (i), los 8 juntos: {ni} declaraciones, {li} líneas\nlos 18: {nt} declaraciones, {lt} líneas\nlo que sólo piden (ii), (iii) y consistencia: {nt - ni} declaraciones, {lt - li} líneas\n\n"
  res := res ++ txtC
  IO.FS.writeFile (dir / "resumen.txt") res
  logInfo m!"{res}"

end ConoTitulares

#cono
