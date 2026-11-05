/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import ROBINSON_PlusPlus

/-!
# SONDEO · la inducción de LISTAS sale de la ordinaria: `listInd` es DERIVABLE en `Prf` sin `listInd` (T69)

✏️ **2026‑11‑05 (ADR‑259): §1–§5 —la prueba— SUBIERON AL BUILD**, tal cual, a `Meta/ListIndAdmisible.lean` (`ROBINSON_PlusPlus.Meta.ListIndAdmisible`). Aquí queda la MEDIDA de §6 —qué reglas de inducción construye la
prueba—, ahora sobre las constantes del build, con sus controles positivos. Lo de abajo describe el sondeo del
2026‑11‑02: «compila», «727 líneas», «la prueba (§1–§5)» son de entonces.

**Fecha:** 2026‑11‑02 · **Por qué:** T69 de `doc/AUDITORIA-SUELO-2026-10-12.md` (Gentzen: primeros pasos medibles), su
segunda medida: «otro [sondeo] de la admisibilidad de listInd» (la primera, el censo de la forma de los axiomas, es
`sondeos/CensoFormaAxiomas.lean`). Un análisis ordinal de `T_Prf` tiene que tratar todas sus reglas; si `listInd` sale
de `ind`, es una regla menos que tratar. Gentzen ya no vive en RPP (ADR‑140): esto es la medida para cuando empiece.

**La pregunta:** ¿es `Prf (listInductionFormula A)` demostrable para TODA `A` —con parámetros, no sólo con `#0`
libre— sin el constructor `Prf.listInd`, ni directamente ni a través de ningún lema que se use?

**Resultado (2026‑11‑02, build del día, Lean v4.35.0): SÍ.**

    theorem listInd_admisible (A : Formula) : Prf (listInductionFormula A)

compila sin `sorry` y sin hipótesis, y la medida de §6 dice que su prueba no construye ningún paso `listInd`. Tampoco
ninguno `p3`: la derivación es intuicionista en la LÓGICA (`Prfᵢ` + `ind` + `qconf`, y `qconf` sólo dentro de
`deduction_aux`), sobre los axiomas de la teoría, que no son todos intuicionistamente inocentes: la tricotomía
(`ax19`) está en el cierre (`#camino`: `prf_cantor_mono_right ⟶ prf_lt_succ_div2`). Corolario:
`prf_list_induction_sin`, la regla derivada de `Meta/ChainPrf.lean` (`prf_list_induction`) con la misma firma y sin
`listInd`. (Los demás usos del constructor en el build, por grep del 2026‑11‑02, son las traducciones, la
decodificación de `SolidezVerificador` y `AxiomasT`.)

**Cómo** (la ruta natural: inducción fuerte sobre el CÓDIGO; `L = nil`, o `L = cons h t` con `t < L`):
* §1 · De Bruijn: lo que hace falta ya estaba (`FOL.Lift0.liftFormula_subst`, `FOL.subst_subst_comm_succ`,
  `FOL.subst_subst_lift_gen`, `FOL.substFormula_liftFormula`, `liftFormula_swap`); aquí, dos instancias, un alias y
  un corolario.
* §2 · Inducción fuerte para TODA `Φ`: `prf_strong_ind_formula Φ : Prf (∀(PSI Φ ⇒ Φ) ⇒ ∀Φ)`. La del build,
  `prf_strong_induction` (`Meta/StrongInductionPrf.lean`), pide `liftFormula 1 Φ = Φ` (ningún parámetro), y una
  instancia de `listInductionFormula` puede tenerlos. La misma prueba —`ind` sobre `PSI Φ`— sin esa hipótesis.
* §3 · Cantor: `σ(pair (σh) t) = pair h (σt)`, `σ(pair 0 t) = pair (σt) 0` y `pair 0 0 = 0`, con `prf_pair_double` y
  `prf_div2_double` (`Meta/Div2ParityPrf.lean`): el polinomio de llegada es el de salida más `2`.
* §4 · Sobreyectividad: `prf_nil_or_consOk L : Prf (L = nil ∨ consOk L)`, por `ind` sobre la ECUACIÓN `consOk (σc)`
  (`σc = cons (carc σc) (cdrc σc)`), con el caso `carc σc = 0 ∨ carc σc = σ(pred ·)` (`prf_zero_or_eq_succ_pred`).
  La del build, `prf_nil_or_cons` (`Meta/SubstfcWitnessPrf.lean`), sale de `prf_list_induction`: de `listInd`.
* §5 · El ensamblaje: con `A[nil]` y el paso en contexto, la inducción fuerte de §2 sobre el código; la cola es menor
  por `prf_cantor_mono_right` (`Meta/CantorMonoPrf.lean`). Lo único delicado, De Bruijn: la instancia del paso
  levantado en `carc #0`, `cdrc #0` (`S_inst`).

**La medida (§6), mecánica:**
* `#induccion` —la orden de `sondeos/InduccionTitulares.lean`, con UN cambio (abajo)— da, sobre el cierre de 2213
  constantes: `listInd: 2 fuera de las traducciones [PrfH_mono, deduction_aux] · traducciones: [prfH_nil_to_prf,
  prf_to_prfH]`. Las cuatro recorren una derivación y reconstruyen cada paso con su constructor homónimo (lo dice su
  fuente, `Meta/HilbertDeduction.lean`; `InduccionTitulares` ya clasificaba así a `deduction_aux`).
* `#induccionSin` corta el cierre en esos recorridos (y en las otras dos traducciones de `InduccionTitulares`):
  `listInd: constructores en el cierre cortado [] · frontera fuera de los recorridos []`; `p3`, igual; `ind`:
  `[Prf.ind, PrfH.ind]`, por `prf_nat_induction` y `prf_strong_ind_formula`. Y `prf_list_induction` no está en el
  cierre COMPLETO. Esa columna («constructores en el cierre cortado») no filtra por espacio de nombres: ninguna
  constante a la que se llegue sin pasar por un recorrido nombra un constructor de `listInd`.
* Controles positivos, vistos fallar en la misma ejecución: `control_con_listInd A := Prf.listInd A` da
  `listInd: 1 fuera de las traducciones [control_con_listInd]` y `Prf.listInd` en el cierre cortado; el
  `prf_nil_or_cons` del build da `[prf_list_induction]` y `prf_list_induction` en el cierre.
* ⚠️ El cambio en la copia de `#induccion`: `esProyecto` mira también `ListIndAdmisible`. Con la copia LITERAL el
  control positivo sale CIEGO (`listInd: 0 fuera de las traducciones []`, medido el 2026‑11‑02 sobre una copia
  aparte): las constantes de un sondeo no están en ninguno de los tres espacios de nombres que mira.
* `ind` (la regla derivada `prf_nat_induction`): la usan `prf_consOk_succ_all` (§4: una ECUACIÓN) y, del build,
  `prf_zero_or_succ`, `prf_add_zero_left`, `prf_add_succ_left`, `prf_le_self_mul_self_all` y
  `prf_mul_le_mono_right` (`#usuarios`, 6); el constructor `PrfH.ind`, `prf_strong_ind_formula` (§2: sobre `PSI A`,
  `A` con un `∀` acotado delante) y los tres recorridos.

**Footprint:** `#print axioms listInd_admisible` = `[propext, Quot.sound]` (y lo mismo `prf_strong_ind_formula`,
`prf_nil_or_consOk` y `prf_list_induction_sin`).

**Lo que NO dice:**
* Que `listInd` sobre en el CÓDIGO: el constructor sigue en `Prf`, `PrfH` y el verificador (`HilbertSeq.Rule.listInd`,
  `ax_lineWF_listInd`), y `AxiomasT` (`Meta/PuenteFOL.lean`) lo lleva como esquema; quitarlo cambiaría la teoría
  codificada, el ancla y `G`. Sí dice que como TEORÍA no añade nada: todo teorema de `Prf` lo es de `Prf` sin
  `listInd`, sustituyendo cada hoja `listInd` por esta derivación (una inducción sobre `Prf` que aquí NO se compila).
* Que el build pueda usarla ya: `prf_list_induction` vive en `Meta/ChainPrf.lean`, por debajo de los módulos que usa
  esta prueba (`Div2ParityPrf`, `CantorMonoPrf`, `StrongInductionPrf`, `BoundedInPrf`, `CodeWitnessPrf`), que importan
  `ChainPrf`. ESTIMACIÓN: un módulo propio y redirigir los usuarios de `prf_list_induction`, uno o dos días, con su ADR.
* Nada del coste en la jerarquía: las instancias de `ind` son las de arriba; cuánto suben a `A` no se ha medido.

**Cuánto:** 727 líneas el sondeo entero; la prueba (§1–§5), 437, y de ellas 339 de código (sin blancos ni
comentarios). La auditoría estimaba «100–300 líneas» (ESTIMACIÓN). Compila en ≈ 6 s (`lake lean`, desde la raíz de
RPP, con el build al día; tres ejecuciones el 2026‑11‑02).

**Cómo re‑ejecutarlo:** `lake lean sondeos/ListIndAdmisible.lean` (desde la raíz de RPP).
-/

open FOL
open ROBINSON_PlusPlus.Minimal.Axioms
open ROBINSON_PlusPlus.Meta.Hilbert
open ROBINSON_PlusPlus.Meta.HilbertDeduction
open ROBINSON_PlusPlus.Meta.ReprPrf
open ROBINSON_PlusPlus.Meta.ArithPrf
open ROBINSON_PlusPlus.Meta.ChainPrf
open ROBINSON_PlusPlus.Meta.NatArithPrf
open ROBINSON_PlusPlus.Meta.NatOrderPrf
open ROBINSON_PlusPlus.Meta.NatMulPrf
open ROBINSON_PlusPlus.Meta.CantorMonoPrf
open ROBINSON_PlusPlus.Meta.StrongInductionPrf
open ROBINSON_PlusPlus.Meta.Div2ParityPrf

namespace ListIndAdmisible

/-! ## §6 · La medida: ¿qué reglas de inducción CONSTRUYE la prueba?

`#print axioms` no lo ve: `ind`, `listInd`, `p3` y `qconf` son constructores de `Prf`, no `axiom`.
`#induccion`, `#camino` y `#usuarios` son copias de las de `sondeos/InduccionTitulares.lean` (la frontera: las constantes
del cierre cuyo VALOR nombra un constructor de la regla en `Prf`, `PrfH` o `HilbertSeq.Rule`; las cuatro traducciones
de allí, aparte), con UN cambio: `esProyecto` mira también `ListIndAdmisible` (sin él, el control positivo sale ciego:
cabecera). `#induccionSin` corta el cierre en las seis constantes que recorren una derivación y reconstruyen cada paso
con el constructor homónimo: las cuatro traducciones, `deduction_aux` y `PrfH_mono`. Si una regla no aparece en el
cierre CORTADO, sólo puede entrar copiada de una derivación que ya la tuviera, y no hay ninguna que la tenga.
⚠️ Para `qconf` el corte NO vale: `deduction_aux` CONSTRUYE un `qconf` en su caso `gen` (así cierra el teorema de
deducción ese caso); por eso `#induccionSin` mide sólo `ind`, `listInd` y `p3`. -/

open Lean Meta Elab Command

namespace Medida

def nombreUsuario (n : Name) : Name := (privateToUserName? n).getD n

/-- ⚠️ El único cambio frente a `InduccionTitulares`: también `ListIndAdmisible`. -/
def esProyecto (n : Name) : Bool :=
  let m := nombreUsuario n
  (`ROBINSON_PlusPlus).isPrefixOf m || (`FOL).isPrefixOf m || (`TheoryFramework).isPrefixOf m
    || (`ListIndAdmisible).isPrefixOf m

def directas (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some ci =>
    let ty := ci.type.getUsedConstants
    let va := ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    ty ++ va
  | none => #[]

/-- El cierre de `raiz` (tipos y valores), sin recorrer las dependencias de las constantes de `corte`. -/
partial def cierreCorte (env : Environment) (raiz : Name) (corte : List Name) : NameSet := Id.run do
  let mut vis : NameSet := {}
  let mut pila := #[raiz]
  while h : pila.size > 0 do
    let n := pila[pila.size - 1]
    pila := pila.pop
    if vis.contains n then continue
    vis := vis.insert n
    if corte.contains n && n != raiz then continue
    for d in directas env n do
      if !vis.contains d then pila := pila.push d
  return vis

def cierre (env : Environment) (raiz : Name) : NameSet := cierreCorte env raiz []

def constructores : List (String × List Name) := [
  ("ind", [``ROBINSON_PlusPlus.Meta.Hilbert.Prf.ind, ``ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.ind,
    ``ROBINSON_PlusPlus.Meta.HilbertSeq.Rule.ind]),
  ("listInd", [``ROBINSON_PlusPlus.Meta.Hilbert.Prf.listInd, ``ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.listInd,
    ``ROBINSON_PlusPlus.Meta.HilbertSeq.Rule.listInd]),
  ("p3", [``ROBINSON_PlusPlus.Meta.Hilbert.Prf.p3, ``ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.p3,
    ``ROBINSON_PlusPlus.Meta.HilbertSeq.Rule.p3]),
  ("qconf", [``ROBINSON_PlusPlus.Meta.Hilbert.Prf.qconf, ``ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.qconf,
    ``ROBINSON_PlusPlus.Meta.HilbertSeq.Rule.qconf])]

/-- Las cuatro traducciones de `InduccionTitulares` (la misma lista). -/
def traducciones : List Name := [
  `ROBINSON_PlusPlus.Meta.HilbertDeduction.prfH_nil_to_prf,
  `ROBINSON_PlusPlus.Meta.HilbertDeduction.prf_to_prfH,
  `ROBINSON_PlusPlus.Meta.HilbertSeq.stepConcl_prf,
  `ROBINSON_PlusPlus.Meta.HilbertSeq.prf_to_derivation]

/-- Y las dos que también recorren una derivación reconstruyendo cada paso (leídas en `Meta/HilbertDeduction.lean`:
    sus casos `ind`, `listInd` y `p3` devuelven el constructor homónimo; `deduction_aux` añade un `qconf` en `gen`). -/
def recorridos : List Name := traducciones ++ [
  `ROBINSON_PlusPlus.Meta.HilbertDeduction.deduction_aux,
  `ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH_mono]

def fronteraDe (env : Environment) (cie : NameSet) (cs : List Name) : Array Name := Id.run do
  let mut out := #[]
  for p in cie.toList do
    if esProyecto p then
      if let some ci := env.find? p then
        if let some v := ci.value? (allowOpaque := true) then
          let us := v.getUsedConstants
          if cs.any (us.contains ·) then out := out.push (nombreUsuario p)
  return out.qsort (fun a b => a.toString < b.toString)

/-- La orden de `InduccionTitulares` (con el `esProyecto` de arriba). -/
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

/-- El cierre CORTADO en los seis recorridos: por regla (`ind`, `listInd`, `p3`), qué constructores suyos están en
    él —sin filtrar por espacio de nombres— y la frontera fuera de los recorridos. -/
elab "#induccionSin " id:ident : command => do
  let env ← getEnv
  let raiz := id.getId
  unless env.contains raiz do throwError "no existe {raiz}"
  let cie := cierreCorte env raiz recorridos
  let mut lineas : Array String := #[]
  for (k, cs) in constructores.filter (·.1 != "qconf") do
    let dentro := cs.filter (cie.contains ·)
    let fr := (fronteraDe env cie cs).toList.filter (fun n => !recorridos.contains n)
    lineas := lineas.push s!"  {k}: constructores en el cierre cortado {dentro.map toString} · frontera fuera de los recorridos {fr.map toString}"
  let pli := (cierre env raiz).contains ``ROBINSON_PlusPlus.Meta.ChainPrf.prf_list_induction
  let rec_ := recorridos.filter (cie.contains ·)
  logInfo m!"{raiz}: cierre cortado de {cie.size} constantes · recorridos alcanzados {rec_.map toString} · `prf_list_induction` en el cierre COMPLETO: {pli}\n{String.intercalate "\n" lineas.toList}"

def deValor (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some ci => ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
  | none => #[]

/-- Un camino MÁS CORTO de `a` a `b` sólo por aristas de VALOR (la de `InduccionTitulares`). -/
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

/-- Los USUARIOS directos de `x` dentro del cierre de `t` (la de `InduccionTitulares`). -/
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

end Medida

/-- CONTROL POSITIVO: la misma fórmula, por el constructor. La medida tiene que verlo. -/
theorem control_con_listInd (A : Formula) : Prf (listInductionFormula A) := Prf.listInd A

end ListIndAdmisible

/-! ### La prueba de la cabecera, y por dónde llega cada constructor -/

#induccion ROBINSON_PlusPlus.Meta.ListIndAdmisible.listInd_admisible
#induccionSin ROBINSON_PlusPlus.Meta.ListIndAdmisible.listInd_admisible
#camino ROBINSON_PlusPlus.Meta.ListIndAdmisible.listInd_admisible ROBINSON_PlusPlus.Meta.Hilbert.Prf.listInd
#camino ROBINSON_PlusPlus.Meta.ListIndAdmisible.listInd_admisible ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.listInd
#usuarios ROBINSON_PlusPlus.Meta.ListIndAdmisible.listInd_admisible ROBINSON_PlusPlus.Meta.NatArithPrf.prf_nat_induction
#usuarios ROBINSON_PlusPlus.Meta.ListIndAdmisible.listInd_admisible ROBINSON_PlusPlus.Meta.HilbertDeduction.PrfH.ind
-- la tricotomía (`ax19`), un axioma de la teoría que no es intuicionistamente inocente: por dónde entra
#camino ROBINSON_PlusPlus.Meta.ListIndAdmisible.listInd_admisible ROBINSON_PlusPlus.Meta.NatMulPrf.prf_lt_trichotomy
-- las dos piezas nuevas, por separado, y el corolario
#induccionSin ROBINSON_PlusPlus.Meta.ListIndAdmisible.prf_nil_or_consOk
#induccionSin ROBINSON_PlusPlus.Meta.ListIndAdmisible.prf_strong_ind_formula
#induccionSin ROBINSON_PlusPlus.Meta.ListIndAdmisible.prf_list_induction_sin

/-! ### Controles positivos: la medida NO es ciega (el constructor directo, y la versión del build de §4) -/

#induccion ListIndAdmisible.control_con_listInd
#induccionSin ListIndAdmisible.control_con_listInd
#induccion ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_nil_or_cons
#induccionSin ROBINSON_PlusPlus.Meta.SubstfcWitnessPrf.prf_nil_or_cons

