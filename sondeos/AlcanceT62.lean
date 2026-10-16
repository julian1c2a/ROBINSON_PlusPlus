/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · el ALCANCE de T62: quién nombra la teoría, el verificador y las reglas

**Fecha:** 2026‑10‑16 · **Por qué:** el paso 2 del orden de ADR‑137 («la medición de alcance que pide T62»), antes del
ADR de diseño (ADR‑144). T62 pide medir «cuántas declaraciones nombran `axioms`, `axiomsCodeT`, `lineWF` o `chainOk`
con un argumento de teoría, y qué cambia en el ancla al añadir una lista»; ADR‑140, además, el coste de parametrizar
las REGLAS (`ind`, `listInd`, `p3`).

**Qué mide.** Para cada GRUPO de constantes, las declaraciones del proyecto (rangos maximales del fuente, como en
`ConoTitulares`) que las nombran DIRECTAMENTE en su tipo o en su valor (`allowOpaque`, y las proyecciones). Es un
RADIO: el número de sitios que un cambio de firma tocaría, no el trabajo; una declaración que sólo pasa el término
sin mirarlo puede no necesitar ningún cambio. Para cada grupo dice además cuántas están en el cono de los 18
titulares (lo que el núcleo necesita) y cuántas en el de D1 (`repr_pos'_prf`), que es lo que habría que portar a un
verificador con parámetro.

**Y comprueba** dos cosas del ancla: si el cierre de `godelCN` y el de `consistencyFormula'` contienen la lista de
axiomas, su código o el ancla.

**Escribe** en `doc/registro/2026-10-16-t62-alcance/` (efecto lateral). Se lanza con
`lake lean sondeos/AlcanceT62.lean` desde la raíz de RPP (54 s).

⚠️ **Lo que infla la cifra:** el término de una prueba de `a ∈ axioms` hecha con `by simp [axioms]` lleva la lista ENTERA,
desplegada. Medido el mismo día: el de `prf_add_zero_t` (`ArithPrf`, tres líneas) nombra 196 constantes, entre ellas los
22 `ax_vpf_*` y los 23 `ax_lineWF_*`. Por eso G4b (`ax_lineWF_thy`, 277) o G7 (`ax_vpf_*`, 298)
salen enormes aquí, y el fuente de las 11 o de las 50 declaraciones que los nombran de verdad es otra cosa. El radio
de EDICIÓN es el textual, `scripts/alcance_t62.bash`.

**Resultado de la ejecución del 2026‑10‑16** (la tabla entera, en `resumen.txt`, y en ADR‑144 §2): los cierres de
`godelCN`, `consistencyFormula'` y `provFormulaC'` NO contienen la lista de axiomas, su código ni el ancla.
-/

open Lean Meta Elab Command

namespace AlcanceT62

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

/-! ## Los grupos y la medida -/

def ax (s : String) : Name := Name.mkStr `ROBINSON_PlusPlus.Minimal.Axioms s

/-- Las constantes de un módulo cuyo último componente empieza por `pre`. -/
def porPrefijo (env : Environment) (modulo : Name) (pre : String) : Array Name := Id.run do
  let mut out := #[]
  for i in [0:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! != modulo then continue
    for c in env.header.moduleData[i]!.constNames do
      match nombreUsuario c with
      | .str _ s => if s.startsWith pre && !(s.contains '.') then out := out.push c
      | _ => pure ()
  return out

def grupos (env : Environment) : List (String × Array Name) :=
  let A := `ROBINSON_PlusPlus.Minimal.Axioms
  let H := `ROBINSON_PlusPlus.Meta.Hilbert
  let lineWFax := (porPrefijo env A "ax_lineWF_") ++ #[ax "ax_chainOk_nil", ax "ax_chainOk_cons"]
  [ ("G1 la lista de axiomas (axioms, axiomsBase, coreAxioms, codingAxioms)",
      #[ax "axioms", ax "axiomsBase", ax "coreAxioms", ax "codingAxioms"]),
    ("G2 el código de la teoría y su ancla (axiomsCodeT, axD, psiD, nD, deltaD, ax_axiomsCodeT_def)",
      #[ax "axiomsCodeT", ax "axD", ax "psiD", ax "nD", ax "deltaD", ax "ax_axiomsCodeT_def"]),
    ("G3 el verificador objeto (lineWF, lineOk, chainOk, provFormulaC', provCodeC')",
      #[ax "lineWF", ax "lineOk", ax "chainOk", `ROBINSON_PlusPlus.Meta.ProofChain.provFormulaC',
        `ROBINSON_PlusPlus.Meta.ProofChain.provCodeC']),
    (s!"G4 los axiomas del verificador que nombran lineWF o chainOk ({lineWFax.size})", lineWFax),
    ("G4b sólo ax_lineWF_thy (el único que nombra axiomsCodeT)", #[ax "ax_lineWF_thy"]),
    ("G5 la regla thy de Lean (Prfᵢ.thy)", #[H ++ `Prfᵢ.thy]),
    ("G6 las reglas que una variante quitaría (Prf.p3, Prf.ind, Prf.listInd y sus homónimas de PrfH)",
      #[H ++ `Prf.p3, H ++ `Prf.ind, H ++ `Prf.listInd,
        `ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.p3, `ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.ind,
        `ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.listInd]),
    (s!"G7 el verificador antiguo (ax_vpf_*, {(porPrefijo env A "ax_vpf_").size}, y validProofFn)",
      (porPrefijo env A "ax_vpf_").push (ax "validProofFn")),
    ("G8 el verificador en el modelo (lineWFT, lineWFN, chainOkL, chainOkN)",
      #[`ROBINSON_PlusPlus.Meta.ModeloCodigo.lineWFT, `ROBINSON_PlusPlus.Meta.ModeloCodigo.lineWFN,
        `ROBINSON_PlusPlus.Meta.ModeloCodigo.chainOkL, `ROBINSON_PlusPlus.Meta.ModeloCodigo.chainOkN])]

elab "#alcance" : command => do
  let env ← getEnv
  let decls ← declaraciones
  let idx ← indiceRangos
  let (enCono, _) ← marcar decls idx (cierre env (titulares.map (·.1)))
  let (enD1, _) ← marcar decls idx (cierre env [``ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf])
  -- las constantes del proyecto, una vez
  let mut todas : Array Name := #[]
  for i in [0:env.header.moduleNames.size] do
    if esModProyecto env.header.moduleNames[i]! then todas := todas ++ env.header.moduleData[i]!.constNames
  let dir : System.FilePath := "doc/registro/2026-10-16-t62-alcance"
  IO.FS.createDirAll dir
  let mut res := "ALCANCE de T62 — 2026-10-16, sondeos/AlcanceT62.lean\n"
  res := res ++ "(usuarios DIRECTOS: declaraciones del fuente cuyo tipo o valor nombra una constante del grupo; es un RADIO, no un trabajo)\n\n"
  res := res ++ "grupo | constantes | declaraciones que las nombran | líneas | en el cono de los 18 | en el cono de D1 | ficheros\n"
  for (g, objetivos) in grupos env do
    let obj : NameSet := objetivos.foldl (fun s n => s.insert n) {}
    let mut usuarios : NameSet := {}
    for c in todas do
      if obj.contains c then continue
      if (directas env c).any obj.contains then usuarios := usuarios.insert c
    let (marca, _) ← marcar decls idx usuarios
    let mut (n, l, nc, n1) := (0, 0, 0, 0)
    let mut fich : NameSet := {}
    let mut lista := s!"# {g}\n# usuarios directos: módulo:inicio-fin (líneas) declaración [C = en el cono de los 18] [D1 = en el de D1]\n"
    for (m, ds) in decls.toList do
      let mk := marca.getD m #[]
      for i in [0:ds.size] do
        if mk[i]! then
          let d := ds[i]!
          let c18 := (enCono.getD m #[])[i]!
          let c1 := (enD1.getD m #[])[i]!
          n := n + 1; l := l + lineasDecl d; fich := fich.insert m
          if c18 then nc := nc + 1
          if c1 then n1 := n1 + 1
          lista := lista ++ s!"{m}:{d.ini}-{d.fin} ({lineasDecl d}) {nombreUsuario d.nombre}{if c18 then " [C]" else ""}{if c1 then " [D1]" else ""}\n"
    IO.FS.writeFile (dir / s!"usuarios-{(g.splitOn " ").head!}.txt") lista
    res := res ++ s!"{g} | {objetivos.size} | {n} | {l} | {nc} | {n1} | {fich.size}\n"
  -- el ancla: ¿qué cierres contienen la teoría?
  let teoria : List Name := [ax "axioms", ax "axiomsBase", ax "axiomsCodeT", ax "ax_axiomsCodeT_def", ax "axD"]
  res := res ++ "\n¿Contiene el cierre la lista de axiomas, su código o el ancla?\n"
  for r in [``ROBINSON_PlusPlus.Meta.DiagonalNumeral.godelCN, ``ROBINSON_PlusPlus.Meta.GodelTwo.consistencyFormula',
            ``ROBINSON_PlusPlus.Meta.ProofChain.provFormulaC'] do
    let cie := cierre env [r]
    let hay := teoria.filter cie.contains
    res := res ++ s!"  {r}: {if hay.isEmpty then "NO" else s!"sí: {hay.map toString}"} ({cie.size} constantes del proyecto en el cierre)\n"
  IO.FS.writeFile (dir / "resumen.txt") res
  logInfo m!"{res}"

end AlcanceT62

#alcance
