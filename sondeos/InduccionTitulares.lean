/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · ¿qué titulares CONSTRUYEN derivaciones con `ind`, `listInd`, `p3` o `qconf`?

**Fecha:** 2026‑10‑12 · **Por qué:** T02 de `doc/AUDITORIA-SUELO-2026-10-12.md`. `AXIOMS.md` §1.1 decía
«D1 y D2 no usan la inducción, verificado con `#print axioms`». Eso se midió sobre los `axiom` de la capa `⊢`
(retirada, ADR‑115). Sobre `Prf`, `#print axioms` no puede verlo: `ind`, `listInd`, `p3` y `qconf` son
CONSTRUCTORES de `Prf`, no `axiom`.

**Qué mide:** para cada titular, las constantes del proyecto de su cierre de dependencias (tipos y valores,
`allowOpaque`) cuyo VALOR nombra directamente un constructor de la regla, en cualquiera de las TRES
representaciones de una derivación: `Prf`, `PrfH` (con contexto, la del teorema de deducción) y
`HilbertSeq.Rule` (las líneas del verificador). Es por ahí por donde un paso con esa regla puede entrar.
* Frontera VACÍA ⇒ la prueba no construye ningún paso con esa regla (medida segura).
* Frontera no vacía ⇒ hay que LEER cada constante: puede CONSTRUIR el paso (`exact Prf.ind A`), TRADUCIRLO de una
  representación a otra (reconstruye cada paso con el constructor homónimo, sin añadir ninguno), o sólo nombrarlo
  en un análisis por casos (un `match`, un `casesOn`). El sondeo separa las cuatro traducciones conocidas; lo demás
  se clasificó leyendo el fuente (abajo).
(Una primera versión excluía los tipos de los ligadores recorriendo el término como ÁRBOL, sin memoria: con la
compartición de los términos de prueba no acababa. `getUsedConstants` recorre el grafo con memoria.)
`#camino a b` da un camino MÁS CORTO de `a` a `b` sólo por aristas de VALOR; `#usuarios t x`, las constantes del
cierre de `t` cuyo valor nombra `x`. Sólo lee el entorno: no evalúa nada del lenguaje objeto (ni `axioms`, ni el
ancla, ni un evaluador). Tarda ≈ 20 s (`lake env lean`, desde la raíz de RPP).

**Resultado de la ejecución del 2026‑10‑12** (re‑ejecutado el 2026‑10‑14 sobre el build de ese día, con el mismo
resultado y dos titulares más, `tarski` y `tarski_semantico`; el detalle, en los mensajes de abajo):
* Fuera de las traducciones, CONSTRUYEN pasos:
  - de `ind` y `listInd`, sólo dos reglas derivadas: `NatArithPrf.prf_nat_induction` (`Prf.ind` y dos MP) y
    `ChainPrf.prf_list_induction` (`Prf.listInd` y dos MP);
  - de `qconf`, el caso `gen` de `deduction_aux` (el teorema de deducción lo necesita) y lemas de siete módulos
    (`ChainPrf`, `ChainOkBoundedPrf`, `CodeWitnessPrf`, `HasWitTcFnPrf`, `SubstfcWitnessPrf`, `EvalNthcPrf` y
    `RunFnBoundedPrf`: 26 en el cierre de D3, cuatro de `ChainPrf` en el de D2); por eso el resultado no da `qconf`
    por titular;
  - y, sólo en `goedel_I_neg`, las líneas que el verificador acepta en el modelo, decodificadas a `Prf`
    (`SolidezVerificador.linea_ind`, `linea_listInd`, `linea_p3`, `linea_qconf`).
  El resto de cada frontera traduce o analiza por casos, leído en su fuente: `deduction_aux` reconstruye los pasos
  `ind`, `listInd` y `p3` que recibe, y `prf_chainOk_track`, `stepConcl_shift` y los `match`/`casesOn` de `Rule` y de
  `lineJustif` analizan por casos.
* `ind` (la regla derivada): la alcanzan D1 (`repr_pos'_prf`), D3 (`d3_prf_real`), `prf_con_imp_godel`,
  `goedel_first_prf`, `goedel_second_prf`, `goedel_I`, `goedel_II`, `goedel_I_neg`, `prf_tarski`, `tarski` y
  `tarski_semantico`; en el cierre de D1 la usan `prf_zero_or_succ` (x = 0 ∨ ∃y x = σy, el Q3 de Robinson, que aquí no
  es axioma), `prf_add_zero_left` (0 + n = n), `prf_add_succ_left` y `prf_mul_le_mono_right`. NO la alcanza D2
  (`d2_prf`): no está en su cierre. (Por lectura, los cuatro usos de D1 son evitables: `0 + n = n` y
  `σm + n = σ(m + n)` salen de `ax6` con `ax4`/`ax5`; Q3, de `ax2`, `ax5`, `ax13` y `ax19`; y la monotonía del
  producto, de `ax13`, `ax10`, `ax12`, Q3 y `ax4`. Que D1 compile sin `ind` no está comprobado.)
* `listInd` (la regla derivada): la alcanzan D2 (por `prf_runFn_concat` y otros ocho de `ChainPrf`), D3,
  `prf_con_imp_godel`, `goedel_second_prf` y `goedel_II`. NO la alcanzan D1, `goedel_first_prf`, `goedel_I`,
  `prf_tarski`, `tarski` ni `tarski_semantico`.
* `p3` (DNE): ningún titular construye un paso `p3`, salvo `goedel_I_neg`, que lo hace al decodificar con `linea_p3`
  las líneas que el verificador acepta en el modelo. En los demás sólo lo nombran las traducciones y los análisis por
  casos: los pasos clásicos de una derivación construida aquí son, a lo sumo, los que traduce de otra que recibe.
* `prf_sound` y `consistencia`: frontera vacía para las cuatro reglas (analizan `Prf`, no construyen).
⚠️ «Alcanza» quiere decir que el término de prueba la nombra por valores, no que el paso sea imprescindible: otra
prueba del mismo enunciado podría evitarlo.

**`#modelo t` (2026‑10‑14, T09, ADR‑135):** la clase de un titular según lo que su prueba usa del MODELO
(`TEOREMAS-E-HIPOTESIS.md` §1). Una constante es «de la semántica» si vive en `FOL.Metamath.Semantics` (`evalFormula`,
`contextSatisfies`…) o en la solidez de `Prf` (`ROBINSON_PlusPlus.Meta.SolidezPrf`), el criterio de T08. Clase (i): el
cierre no nombra ninguna; (ii): las nombra, pero no queda ninguna si no se entra en `consistencia` (sólo sirven para
descargar `ConsistentH`); (iii): las nombra también por otro camino. **Resultado (2026‑10‑14):** (i) D1, D2, D3,
`prf_godelCN_fixedpoint`, `prf_con_imp_godel`, `goedel_first_prf`, `goedel_second_prf` y `prf_tarski`; (ii) `goedel_I`,
`goedel_II` y `tarski`; (iii) `goedel_I_neg`, `godelCN_indecidible`, `godelCN_verdadera`, `con_verdadera`,
`modelo_prov_iff` y `tarski_semantico`. A `consistencia` la clase no se le aplica: es el nodo por el que se corta (con
ella de raíz no se cortaría nada). ⚠️ Es un criterio por ESPACIO DE NOMBRES: una prueba que usara la verdad en ℕ
sin pasar por esos dos no la vería. La aritmética de la metateoría sobre ℕ (`ModeloCodigo`: `lineWFT`, `chainOkN`) no
cuenta como semántica.

**✏️ Re‑ejecutado el 2026‑10‑18 (ADR‑157), 24 s**, con los dos titulares de Rosser y tres `#camino` (la salida, en
`doc/registro/2026-10-18-rosser/`): los 18 de antes dan lo mismo (el cierre de `goedel_I_neg`, 3 531 constantes en vez
de 3 529: W1 es paramétrico desde ADR‑148). `rosser_ext`: clase (i), sin la semántica en el cierre; `rosser`: clase (ii),
90 constantes de la semántica y ninguna sin pasar por `consistencia`. Los dos alcanzan `ind` (por el ∀ acotado:
`prf_bdAll_numeral ⟶ … ⟶ prf_zero_or_succ`), `listInd` (por NegNum: `chainOk_decide ⟶ … ⟶ prf_list_induction`) y
`p3` sólo al decodificar con `linea_p3` las líneas de una prueba con el código de los 142 (W1(ax): `negNum' ⟶ w1Ax ⟶
cadena_buena ⟶ linea_buena ⟶ linea_p3`), como `goedel_I_neg` las del modelo.

**✏️ Y el mismo día, con `lob` (ADR‑159), 22 s:** clase (i), sin la semántica en el cierre (4 935 constantes, con las de Lean); `ind`
y `listInd`, sí; `p3`, no, como `goedel_second_prf` (la salida, en `doc/registro/2026-10-18-lob/`).

**✏️ Y con los corolarios de T78 (ADR‑162), 28 s:** `prf_godel_iff_con` y `goedel_second_formalizado`, clase (i), como
`goedel_second_prf` en `#induccion`; `con_indecidible`, clase (iii) (90 constantes de la semántica, 89 sin pasar por
`consistencia`), y construye `p3` sólo al decodificar el modelo con `linea_p3` (la salida, en
`doc/registro/2026-10-18-t78/`).

**✏️ Y con los cuatro de T75e (ADR‑174), 35 s:** `prf_of_prov_de`, `modelo_prov_iff_de`, `godelCN_verdadera_de` y
`con_verdadera_de`, clase (iii) los cuatro (87, 87, 90 y 90 constantes de la semántica; 87 sin pasar por
`consistencia`); como los de `MNV V₀`, alcanzan `ind`, `listInd`, `p3` y `qconf` al decodificar con W1 (`linea_*`). La
salida, en `doc/registro/2026-10-20-titulares/`.
-/

open Lean Meta Elab Command

namespace InduccionTitulares

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

/-- Cada regla, con sus constructores en las TRES representaciones de una derivación: `Prf`, `PrfH` (con
    contexto, la del teorema de deducción) y `HilbertSeq.Rule` (las líneas del verificador). -/
def constructores : List (String × List Name) := [
  ("ind", [``ROBINSON_PlusPlus.Meta.Hilbert.Prf.ind, ``ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.ind,
    ``ROBINSON_PlusPlus.Meta.HilbertSeq.Rule.ind]),
  ("listInd", [``ROBINSON_PlusPlus.Meta.Hilbert.Prf.listInd, ``ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.listInd,
    ``ROBINSON_PlusPlus.Meta.HilbertSeq.Rule.listInd]),
  ("p3", [``ROBINSON_PlusPlus.Meta.Hilbert.Prf.p3, ``ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.p3,
    ``ROBINSON_PlusPlus.Meta.HilbertSeq.Rule.p3]),
  ("qconf", [``ROBINSON_PlusPlus.Meta.Hilbert.Prf.qconf, ``ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.qconf,
    ``ROBINSON_PlusPlus.Meta.HilbertSeq.Rule.qconf])]

/-- Las TRADUCCIONES entre representaciones: recorren una derivación y reconstruyen cada paso con el
    constructor homónimo, así que nombran todos los constructores sin AÑADIR ninguno. Se listan aparte. -/
def traducciones : List Name := [
  `ROBINSON_PlusPlus.Meta.HilbertDeduction.prfH_nil_to_prf,
  `ROBINSON_PlusPlus.Meta.HilbertDeduction.prf_to_prfH,
  `ROBINSON_PlusPlus.Meta.HilbertSeq.stepConcl_prf,
  `ROBINSON_PlusPlus.Meta.HilbertSeq.prf_to_derivation]

/-- La frontera de `raiz` para una regla: las constantes del proyecto del cierre cuyo VALOR nombra alguno de
    sus constructores. -/
def fronteraDe (env : Environment) (cie : NameSet) (cs : List Name) : Array Name := Id.run do
  let mut out := #[]
  for p in cie.toList do
    if esProyecto p then
      if let some ci := env.find? p then
        if let some v := ci.value? (allowOpaque := true) then
          let us := v.getUsedConstants
          if cs.any (us.contains ·) then out := out.push (nombreUsuario p)
  return out.qsort (fun a b => a.toString < b.toString)

elab "#induccion " id:ident : command => do
  let env ← getEnv
  let raiz := id.getId
  unless env.contains raiz do throwError "no existe {raiz}"
  let cie := cierre env raiz
  let mut lineas : Array String := #[]
  for (k, cs) in constructores do
    let fr := fronteraDe env cie cs
    let (tr, resto) := fr.toList.partition (traducciones.contains ·)
    lineas := lineas.push s!"  {k}: {resto.length} fuera de las traducciones {resto.map toString} · traducciones: {tr.map toString}"
  logInfo m!"{raiz}: cierre de {cie.size} constantes\n{String.intercalate "\n" lineas.toList}"

/-- Constantes que nombra el VALOR de `n` (no su tipo). -/
def deValor (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some ci => ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
  | none => #[]

/-- Un camino MÁS CORTO de `a` a `b` sólo por aristas de VALOR (`b` aparece en el valor del anterior). -/
def camino (env : Environment) (a b : Name) : Option (List Name) := Id.run do
  let mut padre : Std.HashMap Name Name := {}
  let mut vis : NameSet := ({} : NameSet).insert a
  let mut cola := #[a]
  let mut i := 0
  while i < cola.size do
    let n := cola[i]!
    i := i + 1
    if nombreUsuario n == b then
      let mut out := [n]
      let mut m := n
      while m != a do
        m := padre.getD m a
        out := m :: out
      return some out
    for d in deValor env n do
      if !vis.contains d then
        vis := vis.insert d
        padre := padre.insert d n
        cola := cola.push d
  return none

elab "#camino " a:ident b:ident : command => do
  let env ← getEnv
  match camino env a.getId b.getId with
  | some ps => logInfo m!"{a.getId} ⟶ {b.getId}: {ps.length - 1} aristas de valor\n  {String.intercalate "\n  ⟶ " (ps.map (toString ∘ nombreUsuario))}"
  | none => logInfo m!"{a.getId} ⟶ {b.getId}: NINGÚN camino por valores (sólo por tipos, o ninguno)"

/-- Los USUARIOS directos de `x` dentro del cierre de `t`: las constantes cuyo VALOR nombra `x`. -/
elab "#usuarios " t:ident x:ident : command => do
  let env ← getEnv
  let cie := cierre env t.getId
  let mut out : Array Name := #[]
  for p in cie.toList do
    if (deValor env p).contains x.getId then out := out.push (nombreUsuario p)
  let orden := out.qsort (fun a b => a.toString < b.toString)
  logInfo m!"usuarios de {x.getId} en el cierre de {t.getId}: {orden.size}
  {String.intercalate "
  " (orden.toList.map toString)}"

/-- ¿Es una constante de la SEMÁNTICA, la verdad en un modelo? El criterio de T08: `FOL.Metamath.Semantics`
    (`evalFormula`, `evalTerm`, `contextSatisfies`…) o la solidez de `Prf` (`ROBINSON_PlusPlus.Meta.SolidezPrf`). -/
def esSemantica (n : Name) : Bool :=
  let m := nombreUsuario n
  (`FOL.Metamath.Semantics).isPrefixOf m || (`ROBINSON_PlusPlus.Meta.SolidezPrf).isPrefixOf m

/-- El cierre de `raiz` sin entrar en `corte`: si se llega a él, no se recorren sus dependencias. -/
partial def cierreSin (env : Environment) (raiz corte : Name) : NameSet := Id.run do
  let mut vis : NameSet := {}
  let mut pila := #[raiz]
  while h : pila.size > 0 do
    let n := pila[pila.size - 1]
    pila := pila.pop
    if vis.contains n then continue
    vis := vis.insert n
    if n == corte && n != raiz then continue
    for d in directas env n do
      if !vis.contains d then pila := pila.push d
  return vis

/-- La CLASE de un titular según lo que su prueba usa del modelo (T09): (i) nada de la semántica; (ii) la
    semántica sólo a través de `consistencia`, es decir, sólo para descargar `ConsistentH`; (iii) la semántica
    también por otro camino: la verdad en el modelo, más allá de la consistencia. -/
elab "#modelo " id:ident : command => do
  let env ← getEnv
  let raiz := id.getId
  unless env.contains raiz do throwError "no existe {raiz}"
  let c := ``ROBINSON_PlusPlus.Meta.Consistencia.consistencia
  let cie := cierre env raiz
  let todo := cie.toList.filter esSemantica
  let sinC := (cierreSin env raiz c).toList.filter esSemantica
  -- `consistencia` es el nodo por el que se corta: con ella de raíz no se corta nada y saldría (iii) por
  -- construcción (revisión adversarial de ADR‑135); la clase no se le aplica.
  let clase := if raiz == c then "(—) es `consistencia`, el nodo de corte: la clase no se aplica"
    else if todo.isEmpty then "(i) sin el modelo"
    else if sinC.isEmpty then "(ii) el modelo, sólo por `consistencia`"
    else "(iii) la verdad en el modelo, más allá de la consistencia"
  let muestra := ((sinC.map nombreUsuario).take 3).map toString
  logInfo m!"{raiz}: {clase} · semántica en el cierre: {todo.length} · sin pasar por `consistencia`: {sinC.length} {muestra} · `consistencia` en el cierre: {cie.contains c}"

end InduccionTitulares

#induccion ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf
#induccion ROBINSON_PlusPlus.Meta.DerivCondPrf.d2_prf
#induccion ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real
#induccion ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_con_imp_godel
#induccion ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf
#induccion ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf
#induccion ROBINSON_PlusPlus.Meta.SolidezPrf.prf_sound
#induccion ROBINSON_PlusPlus.Meta.Consistencia.consistencia
#induccion ROBINSON_PlusPlus.Meta.Consistencia.goedel_I
#induccion ROBINSON_PlusPlus.Meta.Consistencia.goedel_II
#induccion ROBINSON_PlusPlus.Meta.SolidezVerificador.goedel_I_neg
#induccion ROBINSON_PlusPlus.Meta.TarskiPrf.prf_tarski
#induccion ROBINSON_PlusPlus.Meta.TarskiPrf.tarski
#induccion ROBINSON_PlusPlus.Meta.TarskiPrf.tarski_semantico
-- ✏️ 2026‑10‑18 (ADR‑157): los dos titulares de Rosser.
#induccion ROBINSON_PlusPlus.Meta.Rosser.rosser_ext
#induccion ROBINSON_PlusPlus.Meta.Rosser.rosser
-- ✏️ 2026‑10‑18 (ADR‑159): Löb.
#induccion ROBINSON_PlusPlus.Meta.Lob.lob
-- ✏️ 2026‑10‑18 (ADR‑162): los corolarios de T78.
#induccion ROBINSON_PlusPlus.Meta.GodelCorolarios.prf_godel_iff_con
#induccion ROBINSON_PlusPlus.Meta.GodelCorolarios.goedel_second_formalizado
#induccion ROBINSON_PlusPlus.Meta.GodelCorolarios.con_indecidible
-- ✏️ 2026‑10‑20 (ADR‑174): los cuatro de T75e.
#induccion ROBINSON_PlusPlus.Meta.RigidezEstandar.prf_of_prov_de
#induccion ROBINSON_PlusPlus.Meta.RigidezEstandar.modelo_prov_iff_de
#induccion ROBINSON_PlusPlus.Meta.RigidezEstandar.godelCN_verdadera_de
#induccion ROBINSON_PlusPlus.Meta.RigidezEstandar.con_verdadera_de

/-! ### Por dónde: un camino por VALORES del titular a cada constante de su frontera -/

#camino ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf ROBINSON_PlusPlus.Meta.NatArithPrf.prf_nat_induction
#camino ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf ROBINSON_PlusPlus.Meta.HilbertDeduction.prfH_nil_to_prf
#camino ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf ROBINSON_PlusPlus.Meta.HilbertSeq.stepConcl_prf
#camino ROBINSON_PlusPlus.Meta.DerivCondPrf.d2_prf ROBINSON_PlusPlus.Meta.ChainPrf.prf_list_induction
#camino ROBINSON_PlusPlus.Meta.DerivCondPrf.d2_prf ROBINSON_PlusPlus.Meta.HilbertDeduction.prfH_nil_to_prf
#camino ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real ROBINSON_PlusPlus.Meta.NatArithPrf.prf_nat_induction
#camino ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real ROBINSON_PlusPlus.Meta.ChainPrf.prf_list_induction
#camino ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf ROBINSON_PlusPlus.Meta.NatArithPrf.prf_nat_induction
#camino ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf ROBINSON_PlusPlus.Meta.HilbertDeduction.prfH_nil_to_prf
#camino ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf ROBINSON_PlusPlus.Meta.ChainPrf.prf_list_induction
#camino ROBINSON_PlusPlus.Meta.TarskiPrf.prf_tarski ROBINSON_PlusPlus.Meta.NatArithPrf.prf_nat_induction
#camino ROBINSON_PlusPlus.Meta.SolidezVerificador.goedel_I_neg ROBINSON_PlusPlus.Meta.SolidezVerificador.linea_ind
-- ✏️ 2026‑10‑18 (ADR‑157): por dónde llegan los de Rosser a `ind`, a `listInd` y a la decodificación de `p3`.
#camino ROBINSON_PlusPlus.Meta.Rosser.rosser_ext ROBINSON_PlusPlus.Meta.NatArithPrf.prf_nat_induction
#camino ROBINSON_PlusPlus.Meta.Rosser.rosser_ext ROBINSON_PlusPlus.Meta.ChainPrf.prf_list_induction
#camino ROBINSON_PlusPlus.Meta.Rosser.rosser_ext ROBINSON_PlusPlus.Meta.SolidezVerificador.linea_p3

/-! ### Quién usa las dos reglas derivadas de inducción, dentro de cada cierre -/

#usuarios ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf ROBINSON_PlusPlus.Meta.NatArithPrf.prf_nat_induction
#usuarios ROBINSON_PlusPlus.Meta.DerivCondPrf.d2_prf ROBINSON_PlusPlus.Meta.ChainPrf.prf_list_induction
#usuarios ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real ROBINSON_PlusPlus.Meta.NatArithPrf.prf_nat_induction
#usuarios ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real ROBINSON_PlusPlus.Meta.ChainPrf.prf_list_induction
#usuarios ROBINSON_PlusPlus.Meta.TarskiPrf.prf_tarski ROBINSON_PlusPlus.Meta.NatArithPrf.prf_nat_induction
#camino ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf ROBINSON_PlusPlus.Meta.NatArithPrf.prf_add_zero_left
#camino ROBINSON_PlusPlus.Meta.SolidezVerificador.goedel_I_neg ROBINSON_PlusPlus.Meta.NatArithPrf.prf_nat_induction

/-! ### ¿Qué usa del MODELO cada titular? (T09: las tres clases) -/

#modelo ROBINSON_PlusPlus.Meta.Representability2Prf.repr_pos'_prf
#modelo ROBINSON_PlusPlus.Meta.DerivCondPrf.d2_prf
#modelo ROBINSON_PlusPlus.Meta.PremsBdAllPrf.d3_prf_real
#modelo ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_godelCN_fixedpoint
#modelo ROBINSON_PlusPlus.Meta.GodelTwoPrf.prf_con_imp_godel
#modelo ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_first_prf
#modelo ROBINSON_PlusPlus.Meta.GodelTwoPrf.goedel_second_prf
#modelo ROBINSON_PlusPlus.Meta.TarskiPrf.prf_tarski
#modelo ROBINSON_PlusPlus.Meta.Consistencia.consistencia
#modelo ROBINSON_PlusPlus.Meta.Consistencia.goedel_I
#modelo ROBINSON_PlusPlus.Meta.Consistencia.goedel_II
#modelo ROBINSON_PlusPlus.Meta.TarskiPrf.tarski
#modelo ROBINSON_PlusPlus.Meta.SolidezVerificador.goedel_I_neg
#modelo ROBINSON_PlusPlus.Meta.SolidezVerificador.godelCN_indecidible
#modelo ROBINSON_PlusPlus.Meta.SolidezVerificador.godelCN_verdadera
#modelo ROBINSON_PlusPlus.Meta.SolidezVerificador.con_verdadera
#modelo ROBINSON_PlusPlus.Meta.SolidezVerificador.modelo_prov_iff
#modelo ROBINSON_PlusPlus.Meta.TarskiPrf.tarski_semantico
-- ✏️ 2026‑10‑18 (ADR‑157): los dos titulares de Rosser.
#modelo ROBINSON_PlusPlus.Meta.Rosser.rosser_ext
#modelo ROBINSON_PlusPlus.Meta.Rosser.rosser
-- ✏️ 2026‑10‑18 (ADR‑159): Löb.
#modelo ROBINSON_PlusPlus.Meta.Lob.lob
-- ✏️ 2026‑10‑18 (ADR‑162): los corolarios de T78.
#modelo ROBINSON_PlusPlus.Meta.GodelCorolarios.prf_godel_iff_con
#modelo ROBINSON_PlusPlus.Meta.GodelCorolarios.goedel_second_formalizado
#modelo ROBINSON_PlusPlus.Meta.GodelCorolarios.con_indecidible
-- ✏️ 2026‑10‑20 (ADR‑174): los cuatro de T75e.
#modelo ROBINSON_PlusPlus.Meta.RigidezEstandar.prf_of_prov_de
#modelo ROBINSON_PlusPlus.Meta.RigidezEstandar.modelo_prov_iff_de
#modelo ROBINSON_PlusPlus.Meta.RigidezEstandar.godelCN_verdadera_de
#modelo ROBINSON_PlusPlus.Meta.RigidezEstandar.con_verdadera_de
