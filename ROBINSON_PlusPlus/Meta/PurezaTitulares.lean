/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus.Meta.Consistencia
import ROBINSON_PlusPlus.Meta.TarskiPrf

/-!
# `Meta/PurezaTitulares.lean` — T08: el CONTROL DE PUREZA del cierre de los titulares de la clase (i) (ADR‑143)

**Por qué.** Desde ADR‑120 `ConsistentH` es un teorema (`consistencia`). Una hipótesis `hcon : ConsistentH` se descarga
sola, y el footprint no distingue «basta la consistencia» de «usa la verdad en ℕ»: si un lema de D1–D3 usara la
solidez de `Prf`, `hcon` quedaría de adorno con el MISMO footprint. Hasta hoy, lo único que lo impedía era la forma
del grafo de imports. Este módulo lo COMPRUEBA en cada `lake build`: si falla, el build no compila.

**Qué comprueba.** Para cada titular de la clase (i) de `TEOREMAS-E-HIPOTESIS.md` §1 (`PUROS`), su cierre de
dependencias no contiene ninguna constante de la SEMÁNTICA. El cierre se recorre por tipos y valores (`allowOpaque`),
con los constructores de cada inductivo y el inductivo de cada constructor, y sólo por constantes del proyecto: lo de
Lean no puede nombrar nada de RPP ni de FOL. Las del fichero en curso cuentan como del proyecto (ADR‑149): sin ellas,
un `#pureza` al final de un módulo no veía los lemas del propio módulo. «De la semántica» se decide por ESPACIO DE NOMBRES y por MÓDULO, no por
una lista de nombres: `FOL.Metamath.Semantics` (`FOL/Semantics.lean`: `evalFormula`, `evalTerm`,
`contextSatisfies`…) y `ROBINSON_PlusPlus.Meta.SolidezPrf` (la solidez de `Prf`). Cuenta también una proyección
(`Expr.proj`) sobre una estructura de esos dos, que `getUsedConstants` no ve.
`ModeloCodigo` NO cuenta: es aritmética sobre `Nat`, la de la metateoría, y la necesitaría el W1 paramétrico (T08).

**Controles positivos** (`IMPUROS`): `goedel_I` y `tarski` tienen que DISPARAR, porque llaman a `consistencia`. Si no
disparan, el criterio está ciego y el control falla igual. Visto fallar en los dos sentidos, con un mutante (ADR‑143).

**Lo que NO comprueba.** Una prueba que usara la verdad en ℕ sin pasar por esos dos espacios de nombres no se vería.
Tampoco una estructura de otro módulo que sólo se use por proyección y cuya definición nombre la semántica. Y no fija
el ENUNCIADO de los titulares ni el valor de sus definiciones: eso es T07, que irá en este mismo módulo.

Es el criterio de aceptación de Rosser (ADR‑137): cuando exista, su instancia se añade a `PUROS`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Lean Elab Command

namespace ROBINSON_PlusPlus.Meta.PurezaTitulares

/-- Los titulares de la clase (i): su prueba no usa el modelo. -/
def PUROS : List Name := [
  ``ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf,
  ``ROBINSON_PlusPlus.Meta.DerivCondPrf.d2_prf,
  ``ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real,
  ``ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_godelCN_fixedpoint,
  ``ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_con_imp_godel,
  ``ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf,
  ``ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf,
  ``ROBINSON_PlusPlus.Meta.TarskiPrf.prf_tarski]

/-- Los controles positivos: llaman a `consistencia`, así que su cierre TIENE que nombrar la semántica. -/
def IMPUROS : List Name := [
  ``ROBINSON_PlusPlus.Meta.Consistencia.goedel_I,
  ``ROBINSON_PlusPlus.Meta.TarskiPrf.tarski]

def nombreUsuario (n : Name) : Name := (privateToUserName? n).getD n

def moduloDe (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  env.header.moduleNames[i.toNat]?

def esModuloDelProyecto (m : Name) : Bool :=
  (`ROBINSON_PlusPlus).isPrefixOf m || (`FOL).isPrefixOf m || (`TheoryFramework).isPrefixOf m

/-- ¿Es del proyecto? Por el módulo que la define. Las constantes del fichero que se está compilando no tienen módulo
    de importación (`getModuleIdxFor?` da `none`) y TAMBIÉN cuentan: hasta ADR‑149 se descartaban, y un `#pureza` al
    final de un módulo no recorría los lemas del propio módulo (medido con un mutante: salía PURO). -/
def delProyecto (env : Environment) (n : Name) : Bool :=
  match moduloDe env n with
  | some m => esModuloDelProyecto m
  | none => env.contains n

/-- ¿Es de la SEMÁNTICA? Por espacio de nombres o por módulo. -/
def esSemantica (env : Environment) (n : Name) : Bool :=
  let u := nombreUsuario n
  let porNombre := (`FOL.Metamath.Semantics).isPrefixOf u || (`ROBINSON_PlusPlus.Meta.SolidezPrf).isPrefixOf u
  let porModulo := match moduloDe env n with
    | some m => m == `FOL.Semantics || m == `ROBINSON_PlusPlus.Meta.SolidezPrf
    | none => false
  porNombre || porModulo

/-- Las aristas de `n`: las constantes de su tipo y de su valor, y las del inductivo o sus constructores. -/
def aristas (env : Environment) (n : Name) : Array Name := Id.run do
  let some ci := env.find? n | return #[]
  let mut s := ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then s := s ++ v.getUsedConstants
  match ci with
  | .inductInfo v => s := s ++ v.ctors.toArray
  | .ctorInfo v => s := s.push v.induct
  | _ => pure ()
  return s

/-- ¿Proyecta `n`, en su tipo o en su valor, sobre una estructura de la semántica? -/
def proyectaSemantica (env : Environment) (n : Name) : Option Name := Id.run do
  let some ci := env.find? n | return none
  let prueba (e : Expr) : Option Name :=
    match e.find? (fun x => match x with | .proj s _ _ => esSemantica env s | _ => false) with
    | some (.proj s _ _) => some s
    | _ => none
  if let some s := prueba ci.type then return some s
  if let some v := ci.value? (allowOpaque := true) then return prueba v
  return none

/-- El resultado de recorrer el cierre de `raiz`: cuántas constantes del proyecto tiene y, si nombra la semántica,
    un camino MÁS CORTO hasta la primera constante semántica que encuentra. -/
structure Recorrido where
  tamano : Nat
  camino : Option (List Name)

/-- Recorrido en ANCHURA del cierre de `raiz`, sólo por constantes del proyecto; para en la primera semántica. -/
def recorrer (env : Environment) (raiz : Name) : Recorrido := Id.run do
  let mut padre : Std.HashMap Name Name := {}
  let mut vistos : NameSet := ({} : NameSet).insert raiz
  let mut cola : Array Name := #[raiz]
  let mut i := 0
  while i < cola.size do
    let n := cola[i]!
    i := i + 1
    let mut encontrado : Option Name := none
    if n != raiz && esSemantica env n then encontrado := some n
    else if let some s := proyectaSemantica env n then encontrado := some s
    if let some s := encontrado then
      let mut ruta : List Name := [s]
      let mut m := n
      if s != n then ruta := n :: ruta
      while m != raiz do
        m := padre.getD m raiz
        ruta := m :: ruta
      return { tamano := vistos.size, camino := some ruta }
    for d in aristas env n do
      if !vistos.contains d && delProyecto env d then
        vistos := vistos.insert d
        padre := padre.insert d n
        cola := cola.push d
  return { tamano := vistos.size, camino := none }

def mostrarCamino (ruta : List Name) : String :=
  " ⟶ ".intercalate (ruta.map (toString ∘ nombreUsuario))

/-- El control: los de `puros` no pueden nombrar la semántica; los de `impuros` TIENEN que nombrarla. -/
def comprobar (puros impuros : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut informe : Array String := #[]
  let mut fallos : Array String := #[]
  for t in puros do
    unless env.contains t do fallos := fallos.push s!"{t}: NO EXISTE (¿renombrado?)"; continue
    let r := recorrer env t
    match r.camino with
    | none => informe := informe.push s!"  ✓ PURO    {nombreUsuario t} ({r.tamano} constantes del proyecto en el cierre)"
    | some ruta => fallos := fallos.push s!"{nombreUsuario t} nombra la semántica:\n      {mostrarCamino ruta}"
  for t in impuros do
    unless env.contains t do fallos := fallos.push s!"{t}: NO EXISTE (¿renombrado?)"; continue
    let r := recorrer env t
    match r.camino with
    | some ruta => informe := informe.push s!"  ✓ IMPURO  {nombreUsuario t}, como se espera: {mostrarCamino ruta}"
    | none => fallos := fallos.push s!"{nombreUsuario t} NO nombra la semántica, y TIENE que nombrarla (llama a `consistencia`): el criterio está CIEGO"
  if fallos.isEmpty then
    logInfo m!"T08 · pureza del cierre (ADR‑143): {puros.length} puros y {impuros.length} controles positivos\n{"\n".intercalate informe.toList}"
  else
    throwError m!"⛔ T08 · el control de pureza FALLA (ADR‑143):\n  {"\n  ".intercalate fallos.toList}\n{"\n".intercalate informe.toList}"

/-- `#pureza_titulares`: el control, sobre `PUROS` e `IMPUROS`. -/
elab "#pureza_titulares" : command => comprobar PUROS IMPUROS

/-- `#pureza a b … | x y …`: el mismo control sobre listas dadas, para los mutantes y para un titular nuevo. -/
syntax (name := purezaDe) "#pureza " ident* " | " ident* : command

@[command_elab purezaDe] def elabPurezaDe : CommandElab := fun stx => do
  let resolver (i : Syntax) : CommandElabM Name := liftCoreM (resolveGlobalConstNoOverload i)
  let puros ← stx[1].getArgs.toList.mapM resolver
  let impuros ← stx[3].getArgs.toList.mapM resolver
  comprobar puros impuros

/-! ### El recorrido DENTRO de un módulo, vigilado (ADR‑149)

`#pureza` se usa al final de los módulos de Rosser sobre teoremas del MISMO fichero (ADR‑147). Este par es su control
positivo: `mutanteLocal` sólo nombra un lema de este fichero, y ese lema llama a `consistencia`, que usa el modelo.
Si el recorrido dejara de seguir las constantes del fichero en curso, `mutanteLocal` saldría puro y el build no
compilaría. Visto fallar: antes del arreglo de `delProyecto`, el mismo mutante salía PURO. -/

theorem auxLocalSemantico : ROBINSON_PlusPlus.Meta.Hilbert.ConsistentH :=
  ROBINSON_PlusPlus.Meta.Consistencia.consistencia

theorem mutanteLocal : ROBINSON_PlusPlus.Meta.Hilbert.ConsistentH := auxLocalSemantico

#pureza | mutanteLocal

end ROBINSON_PlusPlus.Meta.PurezaTitulares

#pureza_titulares
