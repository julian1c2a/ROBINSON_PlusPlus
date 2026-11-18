#!/bin/bash
# check-indice.bash — el ÍNDICE de las constantes de RPP, y lo que nadie usa de FOL (L5-11 y FOL0912:B-5, ADR-254).
#
# ⛔ POR QUÉ EXISTE. «Antes de construir, buscar» se repetía en seis ADR (L5-11, ronda 1 de la auditoría de la base): se
# volvía a construir lo que ya estaba, porque no había dónde buscarlo salvo con grep sobre el texto, que no ve el nombre
# completo que da un `namespace` ni el enunciado que elabora Lean. Y de la librería FOL, 96 de 157 declaraciones no las
# usaba nadie (B-5 de la auditoría de FOL del 2026-09-12), sin que lo dijera ningún sitio. Las dos decisiones del
# propietario (2026-11-04): el índice (nombre, módulo, enunciado) de todas las constantes de RPP y FOL, regenerado y
# comprobado en cada run; y lo que nadie usa de FOL, medido y etiquetado, sin borrar.
#
# QUÉ ESCRIBE. Del entorno de Lean —un fichero generado que importa CADA módulo de RPP, FOL y TheoryFramework, como
# check-choice.bash—, cada constante DECLARADA: con rango de declaración en su fuente y que Lean no genere (ni
# recursores, ni `casesOn`, ni `match_N`, ni ecuaciones, ni `injEq`, ni `ctorElim`…: las reglas de
# `Lean.isAutoDeclOrPrivate_Internal`, de Lean/AutoDecl.lean, salvo que una privada cuenta por su nombre de usuario).
#   doc/indice.tsv               las de RPP, una por línea: «nombre · clase · módulo · enunciado», el enunciado como lo
#                                imprime Lean con los nombres COMPLETOS (`pp.fullNames`: no depende de los `open` ni de
#                                los `export`), en una línea. Las de FOL y TheoryFramework están en
#                                ../FOL/doc/indice.tsv, que genera y comprueba el check-indice.bash de FOL, en su CI.
#   doc/control/fol-sin-uso.tsv  las de FOL y TheoryFramework que NINGUNA otra constante de las tres librerías nombra,
#                                ni en su tipo ni en su valor: «módulo · nombre · clase · etiqueta». Un constructor o un
#                                campo cuentan como su tipo, y lo que Lean genera con una declaración (su `match_N`, sus
#                                ecuaciones, su `proof_N`), como ella. La etiqueta dice por qué puede no ser basura:
#                                  vigilada   tiene fila en check-footprints.bash: un titular, una hoja a propósito
#                                  simp       lleva el atributo: simp puede usarla sin dejar rastro en el término
#                                             (feedback «simp con un lema rfl NO deja prueba»)
#                                  instancia  la usaría la resolución de instancias
#                                  meta       sintaxis o elaborador: la usa el analizador, no un término
#                                  —          ninguna de las anteriores
#                                No se cuentan los sondeos, el libro ni los consumidores archivados (ADR-216); y un
#                                bloque `mutual` se usa a sí mismo.
#   doc/contratos/CAPA.tsv       ✏️ 2026-11-18 (B1 paso 6, ADR-272): el CONTRATO de cada capa de doc/control/capas.tsv
#                                (y de FOL, la de debajo de todas): las constantes declaradas en un módulo de la capa que
#                                nombra, en su tipo o en su valor, una constante declarada en un módulo de RPP de OTRA
#                                capa —con el mismo «dueño» y la misma medida de uso que la tabla de arriba—, una por
#                                línea: «nombre · módulo · huella del tipo · las capas que la usan». La huella es el
#                                `Expr.hash` del tipo (en un inductivo, con los de sus constructores), la de las huellas de
#                                ADR-261 y la de T07: cambia si cambia el enunciado, no si sólo cambia la notación. Así, un
#                                cambio de la API de una capa baja, o un uso nuevo entre dos capas, se ve en el diff.
#                                El enunciado de cada una, en doc/indice.tsv.
#
# ⭐ Las dos tablas se comparan con lo que se GENERA, línea a línea: cualquier diferencia es rojo. Se rehacen con
# `--rehacer` en el mismo commit que cambia una declaración (como DEPENDENCIES.md con gen-dependencies.py); un push de
# FOL que cambia lo que nadie usa deja rojo el run de RPP hasta el commit de RPP que lo acompaña (M-12), como
# doc/control/choice.tsv.
#
# 🔑 CALIBRACIÓN (feedback de los controles que no comprueban nada): el fichero generado declara seis constantes de
# prueba —un teorema, otro que lo usa, una privada, un inductivo con dos constructores, una función por casos sobre él y
# una recursiva—; el control exige ver en el índice exactamente esas ocho declaraciones (con los dos constructores) y sus
# enunciados (ni el recursor, ni `casesOn`, ni `match_1`, ni `injEq`), que el filtro de las generadas quite él solo las
# de prueba sin rango (la falta de rango es un segundo filtro, y sin esto no se le vería fallar al primero), que se
# generen al menos cuatro constantes más, y que la medida de uso diga cuáles se usan (la recursiva, no: sólo la nombra
# lo que Lean genera con ella, y sin el «dueño» saldría usada). Si el censo no corre o no llega al final (la línea
# FIN), es rojo. ✏️ ADR-272, los contratos: dos constantes de prueba más, de la pseudocapa CALIB —`calibC` nombra `Prf`
# (C1) y `Formula` (FOL) sólo en su TIPO; `calibV`, `Prfᵢ` (C1) sólo en su VALOR— tienen que dar exactamente esas tres
# filas (y ninguna por los usos entre las de prueba, que son del mismo fichero); el cruce de capas (el awk), con unos usos
# inventados, lo esperado —el filtro de la misma capa, que en la calibración de Lean taparía el de módulo—; un módulo sin
# fila en doc/control/capas.tsv, rojo; y cada capa de C0 a C6, y FOL, con contrato (si una se queda sin él, nadie la usa).
#
# 🔧 Desde la raíz de RPP, con el build al día (`lake build` y `lake build "@FOL/FOL" "@FOL/TheoryFramework"`), desde
# PowerShell o desde un bash con `lake` en el PATH.
#
#   bash check-indice.bash            # genera y compara con las dos tablas
#   bash check-indice.bash --rehacer  # además, las reescribe con lo generado
#
# Para buscar antes de construir: `grep -i 'patrón' doc/indice.tsv ../FOL/doc/indice.tsv` (AI-GUIDE, «Antes de
# construir, buscar»).

set -uo pipefail
export PATH="/usr/bin:$PATH"
cd "$(dirname "$0")" || exit 2

INDICE=doc/indice.tsv
SINUSO=doc/control/fol-sin-uso.tsv
REHACER=0
[ "${1:-}" = "--rehacer" ] && REHACER=1

echo "════ EL ÍNDICE DE LAS CONSTANTES DE RPP, LO QUE NADIE USA DE FOL Y LOS CONTRATOS DE LAS CAPAS ════"

if ! command -v lake >/dev/null 2>&1; then
  echo "  ⚠️  SIN MEDIR — 'lake' no está en el PATH de este shell. Un control que no se ejecuta NO es un control."
  exit 2
fi

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
# (Lean es un programa de Windows en la máquina de desarrollo: las rutas que lee, en su forma; en Linux, tal cual)
win() { cygpath -m "$1" 2>/dev/null || printf '%s' "$1"; }
LEANFILE="$TMP/Indice.lean"
MODS="$TMP/modulos.txt"
{
  ( find ROBINSON_PlusPlus -name '*.lean' ; echo ROBINSON_PlusPlus.lean )
  ( cd ../FOL && find FOL TheoryFramework -name '*.lean' ; echo FOL.lean ; echo TheoryFramework.lean )
} | sed -e 's/\.lean$//' -e 's|/|.|g' | LC_ALL=C sort -u > "$MODS"
NMODS=$(grep -c . "$MODS")
if [ "$NMODS" -lt 100 ]; then
  echo "  ❌ sólo $NMODS módulos: la lista de ficheros no se pudo leer (¿falta ../FOL?)."
  exit 1
fi
# las que tienen fila en check-footprints.bash (la etiqueta «vigilada»)
VIGILADAS="$TMP/vigiladas.txt"
sed -n "/^read -r -d '' TABLA <<'EOF'\$/,/^EOF\$/p" check-footprints.bash | grep '|' | cut -d'|' -f1 > "$VIGILADAS"
NVIG=$(grep -c . "$VIGILADAS")
if [ "$NVIG" -lt 100 ]; then
  echo "  ❌ sólo $NVIG filas de check-footprints.bash: no pude leer su tabla."
  exit 1
fi
{
  echo "import Lean"
  sed 's/^/import /' "$MODS"
  cat <<'EOF'
open Lean Meta
-- (las notaciones de las fórmulas de FOL, `¬ ∧ ∨`, son `scoped` desde ADR-258: se abren para que los enunciados se
-- impriman como se escriben)
open scoped FOL

namespace IndiceCalib
-- la calibración: el índice tiene que ver estas ocho declaraciones (con los dos constructores), y no lo que Lean
-- genera con ellas; y la medida de uso, que se usan `calibT` (la usa `calibU`) y `CalibI` (la usa `calibM`), y nada
-- más: `calibR` sólo la nombra lo que Lean genera con ella (su `_sunfold`), y eso es ella misma
theorem calibT (n : Nat) : n + 0 = n := rfl
theorem calibU : 3 + 0 = 3 := calibT 3
private def calibP : Nat := 1
inductive CalibI where
  | uno
  | dos (n : Nat)
def calibM : CalibI → Nat
  | .uno => 0
  | .dos n => n
def calibR : Nat → Nat
  | 0 => 0
  | n + 1 => calibR n
-- (ADR-272) la calibración de los contratos: `Prf` y `Formula`, sólo en el tipo (la prueba es `trivial`); `Prfᵢ`, sólo
-- en el valor (el tipo es `Prop`)
theorem calibC : (fun _ : Prop => True) (∀ φ, ROBINSON_PlusPlus.Meta.Hilbert.Prf φ) := trivial
def calibV : Prop := ∀ φ, ROBINSON_PlusPlus.Meta.Hilbert.Prfᵢ φ
end IndiceCalib

/-- La huella de una constante en un contrato de capa (ADR-272): el `Expr.hash` de su tipo; en un inductivo, con el
    nombre y el tipo de cada constructor (los constructores son del inductivo: cambiarlos cambia su API). -/
def contratoHuella (env : Environment) (ci : ConstantInfo) : UInt64 :=
  match ci with
  | .inductInfo v =>
    v.ctors.foldl (fun h c => mixHash h (mixHash (hash c) (((env.find? c).map (·.type.hash)).getD 0))) ci.type.hash
  | _ => ci.type.hash

def indiceRaiz (m : Name) : Option String :=
  let r := m.getRoot.toString
  if r == "ROBINSON_PlusPlus" then some "RPP" else if r == "FOL" then some "FOL"
  else if r == "TheoryFramework" then some "TF" else none

/-- ¿la genera Lean? Las reglas de `Lean.isAutoDeclOrPrivate_Internal` (Lean/AutoDecl.lean), salvo que una privada
    cuenta por su nombre de usuario: aquélla las da todas por generadas. -/
partial def indiceGenerada (env : Environment) (d : Name) : Bool :=
  let u := (privateToUserName? d).getD d
  if isPrivateName d && u.isAnonymous then false
  else if d.hasMacroScopes || u.isInternal || isReservedName env d then true
  else match d with
    | .str n s =>
      indiceGenerada env n || s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "unsafe_"
        || s.startsWith "grind_"
        || (env.isConstructor n && ["injEq", "inj", "sizeOf_spec", "elim", "noConfusion"].contains s)
        || (match env.find? n with
            | some (.inductInfo _) =>
              s.startsWith "brecOn_" || s.startsWith "below_"
                || ["casesOn", "recOn", "brecOn", "below", "ndrec", "ndrecOn", "noConfusionType", "noConfusion",
                    "ofNat", "toCtorIdx", "ctorIdx", "ctorElim", "ctorElimType"].contains s
                || (isSubobjectField? env n (.mkSimple s)).isSome
            | _ => false)
    | _ => false

/-- el enunciado en una línea: los saltos y los tabuladores, espacios; los espacios seguidos, uno -/
def indiceLinea (s : String) : String := Id.run do
  let mut out := ""
  let mut esp := false
  for ch in s.toList do
    let ch := if ch == '\n' || ch == '\t' || ch == '\r' then ' ' else ch
    if ch == ' ' then
      unless esp do out := out.push ' '
      esp := true
    else
      out := out.push ch
      esp := false
  return out

#eval show MetaM Unit from do
  let env ← getEnv
  let simps ← getSimpTheorems
  let some rutaI ← IO.getEnv "INDICE_RPP" | throwError "falta INDICE_RPP"
  let some rutaS ← IO.getEnv "INDICE_SINUSO" | throwError "falta INDICE_SINUSO"
  let some rutaV ← IO.getEnv "INDICE_VIGILADAS" | throwError "falta INDICE_VIGILADAS"
  let vigiladas : Std.HashSet String := Std.HashSet.ofList (← IO.FS.lines rutaV).toList
  let repoDe (c : Name) : Option (String × String) := match env.getModuleIdxFor? c with
    | some i =>
      let m := env.header.moduleNames[i.toNat]!
      (indiceRaiz m).map (fun r => (r, m.toString))
    | none => if (`IndiceCalib).isPrefixOf ((privateToUserName? c).getD c) then some ("CALIB", "_calibracion") else none
  -- 1. las declaradas
  let mut decl : Std.HashMap Name (String × String) := {}
  let mut nGen : Std.HashMap String Nat := {}
  let mut sinRango : Array Name := #[]
  for (c, ci) in env.constants.toList do
    let some (repo, modulo) := repoDe c | continue
    let gen := (match ci with | .recInfo _ | .quotInfo _ => true | _ => false)
      || isAuxRecursor env c || isNoConfusion env c || isRecCore env c || isMatcherCore env c || indiceGenerada env c
    if gen then
      nGen := nGen.insert repo ((nGen.getD repo 0) + 1)
      continue
    if (← findDeclarationRanges? c).isNone then
      sinRango := sinRango.push c
      continue
    decl := decl.insert c (repo, modulo)
  -- el dueño de una constante: la declarada a la que pertenece; la de un constructor o un campo, su tipo
  let dueno (c : Name) : Name := Id.run do
    let mut p := c
    while !p.isAnonymous && !decl.contains p do p := p.getPrefix
    if p.isAnonymous then return c
    match env.find? p with
    | some (.ctorInfo v) => return v.induct
    | _ =>
      match env.getProjectionFnInfo? p with
      | some pi =>
        match env.find? pi.ctorName with
        | some (.ctorInfo v) => return v.induct
        | _ => return p
      | none => return p
  -- 2. el uso: qué dueño nombra a qué otro, en el tipo o en el valor (1 RPP, 2 FOL, 4 TF, 8 la calibración)
  let bit (r : String) : Nat := if r == "RPP" then 1 else if r == "FOL" then 2 else if r == "TF" then 4 else 8
  let mut usada : Std.HashMap Name Nat := {}
  -- (ADR-272) y, para los contratos de las capas, de qué MÓDULO de RPP (o de la calibración) se usa cada dueño de otro
  let mut usos : Std.HashSet (Name × String) := {}
  let mut sinValor := 0
  for (c, ci) in env.constants.toList do
    let some (repo, modC) := repoDe c | continue
    let dc := dueno c
    let val := ci.value? (allowOpaque := true)
    if val.isNone && (ci.isTheorem || ci.isDefinition) then sinValor := sinValor + 1
    for u in ci.type.getUsedConstants ++ ((val.map (·.getUsedConstants)).getD #[]) do
      let du := dueno u
      if du != dc && decl.contains du then
        usada := usada.insert du ((usada.getD du 0) ||| bit repo)
        if repo == "RPP" || repo == "CALIB" then
          if let some (_, mu) := decl.get? du then
            if mu != modC then usos := usos.insert (du, modC)
  -- 3. las filas
  let mut indice : Array String := #[]
  let mut sinUso : Array String := #[]
  let mut calib : Array String := #[]
  let mut nDecl : Std.HashMap String Nat := {}
  let mut nUsoRPP : Std.HashMap String Nat := {}
  let mut nUsoDentro : Std.HashMap String Nat := {}
  let mut nSinUso : Std.HashMap String Nat := {}
  let mut nCortados := 0
  for (c, (repo, modulo)) in decl.toList do
    let some ci := env.find? c | continue
    let u := (privateToUserName? c).getD c
    let esMeta := match ci.type.getAppFn.constName? with
      | some h => h.getRoot == `Lean
      | none => false
    let clase := match ci with
      | .thmInfo _ => "teorema"
      | .axiomInfo _ => "axioma"
      | .opaqueInfo _ => "opaca"
      | .ctorInfo _ => "constructor"
      | .inductInfo _ => if isClass env c then "clase" else if isStructure env c then "estructura" else "inductivo"
      | .defnInfo _ =>
        if isInstanceCore env c then "instancia"
        else if (env.getProjectionFnInfo? c).isSome then "campo"
        else if esMeta then "meta" else "def"
      | _ => "otra"
    let clase := if isPrivateName c then clase ++ "·privada" else clase
    nDecl := nDecl.insert repo ((nDecl.getD repo 0) + 1)
    if repo == "RPP" || repo == "CALIB" then
      let f ← withOptions (fun o => pp.fullNames.set o true) (ppExpr ci.type)
      let mut txt := indiceLinea (f.pretty 100000)
      -- (un enunciado de más de 4000 caracteres se corta, y lo dice)
      if txt.length > 4000 then
        nCortados := nCortados + 1
        txt := String.ofList (txt.toList.take 4000) ++ s!" …[+{txt.length - 4000}]"
      let fila := s!"{u}\t{clase}\t{modulo}\t{txt}"
      if repo == "CALIB" then calib := calib.push s!"CALIB\tI\t{fila}" else indice := indice.push fila
    if (repo == "FOL" || repo == "TF" || repo == "CALIB") && dueno c == c then
      let m := usada.getD c 0
      if m &&& 1 != 0 then nUsoRPP := nUsoRPP.insert repo ((nUsoRPP.getD repo 0) + 1)
      else if m != 0 then nUsoDentro := nUsoDentro.insert repo ((nUsoDentro.getD repo 0) + 1)
      if m == 0 then
        nSinUso := nSinUso.insert repo ((nSinUso.getD repo 0) + 1)
        let etiqueta :=
          if vigiladas.contains u.toString then "vigilada"
          else if simps.isLemma (.decl c) then "simp"
          else if clase.startsWith "instancia" then "instancia"
          else if clase.startsWith "meta" then "meta"
          else "—"
        let fila := s!"{modulo}\t{u}\t{clase}\t{etiqueta}"
        if repo == "CALIB" then calib := calib.push s!"CALIB\tS\t{fila}" else sinUso := sinUso.push fila
      else if repo == "CALIB" then calib := calib.push s!"CALIB\tU\t{u}"
  IO.FS.writeFile rutaI ("\n".intercalate indice.toList ++ "\n")
  IO.FS.writeFile rutaS ("\n".intercalate sinUso.toList ++ "\n")
  -- (ADR-272) los usos entre módulos: «dueño usado · su módulo · su huella · el módulo que lo usa»
  let some rutaU ← IO.getEnv "INDICE_USOS" | throwError "falta INDICE_USOS"
  let mut lineasU : Array String := #[]
  for (du, mc) in usos.toList do
    let some (_, md) := decl.get? du | continue
    let some ci := env.find? du | continue
    lineasU := lineasU.push s!"{(privateToUserName? du).getD du}\t{md}\t{contratoHuella env ci}\t{mc}"
  IO.FS.writeFile rutaU ("\n".intercalate lineasU.toList ++ "\n")
  IO.println s!"USOS\t{lineasU.size}"
  for l in calib do IO.println l
  for r in ["RPP", "FOL", "TF", "CALIB"] do
    IO.println s!"TOTAL\t{r}\t{nDecl.getD r 0}\t{nGen.getD r 0}\t{nUsoRPP.getD r 0}\t{nUsoDentro.getD r 0}\t{nSinUso.getD r 0}"
  IO.println s!"SINRANGO\t{sinRango.size}\t{" ".intercalate ((sinRango.toList.map toString).take 10)}"
  -- (las de prueba que no tienen rango tiene que verlas generadas el primer filtro: si no, no se le ve fallar)
  let calibSinRango := sinRango.filter (fun c => (`IndiceCalib).isPrefixOf ((privateToUserName? c).getD c))
  IO.println s!"SINRANGOCALIB\t{calibSinRango.size}\t{" ".intercalate (calibSinRango.toList.map toString)}"
  IO.println s!"SINVALOR\t{sinValor}"
  IO.println s!"CORTADOS\t{nCortados}"
  IO.println "FIN"
EOF
} > "$LEANFILE"

GEN_I="$TMP/indice.tsv"; GEN_S="$TMP/sinuso.tsv"
T0=$(date +%s)
SALIDA=$(INDICE_RPP="$(win "$TMP/indice.crudo")" INDICE_SINUSO="$(win "$TMP/sinuso.crudo")" \
  INDICE_VIGILADAS="$(win "$VIGILADAS")" INDICE_USOS="$(win "$TMP/usos.crudo")" lake env lean "$(win "$LEANFILE")" 2>&1)
RC=$?
T1=$(date +%s)
FAIL=0
# (sin tubería hacia `grep -q`: con pipefail, el SIGPIPE de printf la daría por fallida)
if [ "$RC" != "0" ] || ! grep -qx 'FIN' <<< "$SALIDA"; then
  echo "  ❌ el censo no llegó al final (lake env lean salió con $RC):"
  printf '%s\n' "$SALIDA" | grep -v '^CALIB' | head -20 | sed 's/^/      /'
  exit 1
fi
echo "  censo: $NMODS módulos, $((T1 - T0)) s"
tr -d '\r' < "$TMP/indice.crudo" | grep . | LC_ALL=C sort > "$GEN_I"
tr -d '\r' < "$TMP/sinuso.crudo" | grep . | LC_ALL=C sort > "$GEN_S"

# la calibración: el índice, exactamente estas siete (con su enunciado); el uso, exactamente éste
CAL_I=$(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "CALIB" && $2 == "I" { print $3 "\t" $4 "\t" $6 }' | LC_ALL=C sort)
ESP_I=$(LC_ALL=C sort <<'EOF'
IndiceCalib.CalibI	inductivo	Type
IndiceCalib.CalibI.dos	constructor	Nat → IndiceCalib.CalibI
IndiceCalib.CalibI.uno	constructor	IndiceCalib.CalibI
IndiceCalib.calibC	teorema	(fun x => True) (∀ (φ : Formula), ROBINSON_PlusPlus.Meta.Hilbert.Prf φ)
IndiceCalib.calibM	def	IndiceCalib.CalibI → Nat
IndiceCalib.calibP	def·privada	Nat
IndiceCalib.calibR	def	Nat → Nat
IndiceCalib.calibT	teorema	∀ (n : Nat), n + 0 = n
IndiceCalib.calibU	teorema	3 + 0 = 3
IndiceCalib.calibV	def	Prop
EOF
)
if [ "$CAL_I" = "$ESP_I" ]; then
  echo "  ✓ calibración del índice: las diez declaraciones de prueba (dos constructores), con su enunciado, y nada más"
else
  echo "  ❌ calibración del índice: no ve exactamente las declaraciones de prueba —no comprueba lo que dice—:"
  diff <(printf '%s\n' "$ESP_I") <(printf '%s\n' "$CAL_I") | sed 's/^/      /'
  FAIL=1
fi
CAL_U=$(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "CALIB" && $2 == "U" { print "usada " $3 } $1 == "CALIB" && $2 == "S" { print "sin uso " $4 }' | LC_ALL=C sort)
ESP_U=$(LC_ALL=C sort <<'EOF'
sin uso IndiceCalib.calibC
sin uso IndiceCalib.calibV
sin uso IndiceCalib.calibM
sin uso IndiceCalib.calibP
sin uso IndiceCalib.calibR
sin uso IndiceCalib.calibU
usada IndiceCalib.CalibI
usada IndiceCalib.calibT
EOF
)
if [ "$CAL_U" = "$ESP_U" ]; then
  echo "  ✓ calibración del uso: calibT y CalibI, usadas; calibU, calibP, calibM y calibR (la nombra su _sunfold), no"
else
  echo "  ❌ calibración del uso: la medida no dice lo esperado:"
  diff <(printf '%s\n' "$ESP_U") <(printf '%s\n' "$CAL_U") | sed 's/^/      /'
  FAIL=1
fi
SRCAL=$(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "SINRANGOCALIB" { print $2 "\t" $3 }')
if [ "${SRCAL%%	*}" != "0" ]; then
  echo "  ❌ calibración: de las de prueba, éstas sólo las quitó la falta de rango, no el filtro de las generadas: ${SRCAL#*	}"
  FAIL=1
fi
GENCAL=$(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "TOTAL" && $2 == "CALIB" { print $4 }')
if [ "${GENCAL:-0}" -lt 4 ]; then
  echo "  ❌ calibración: sólo ${GENCAL:-0} constantes generadas con las de prueba (el recursor, casesOn, match_1…): el filtro no las ve."
  FAIL=1
fi
SINV=$(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "SINVALOR" { print $2 }')
if [ "${SINV:-x}" != "0" ]; then
  echo "  ❌ $SINV teoremas o definiciones sin valor accesible: la medida de uso no los ve."
  FAIL=1
fi
printf '%s\n' "$SALIDA" | awk -F'\t' '
  $1 == "TOTAL" && $2 != "CALIB" { printf "  %-4s %5d declaradas (%5d generadas, fuera)", $2, $3, $4
    if ($2 != "RPP") printf " · %4d las usa RPP · %4d sólo FOL o TF · %4d nadie", $5, $6, $7
    printf "\n" }
  $1 == "SINRANGO" { printf "  %d constantes sin rango de declaración (generadas), fuera: %s\n", $2, $3 }
  $1 == "CORTADOS" && $2 > 0 { printf "  %d enunciados de más de 4000 caracteres, cortados (lo dice la línea)\n", $2 }'
echo "  lo que nadie usa, por etiqueta: $(awk -F'\t' '{ n[$4]++ } END { for (e in n) printf "%s %d · ", e, n[e] }' "$GEN_S" | sed 's/ · $//')"

# ── (ADR-272) los CONTRATOS de las capas: de los usos entre módulos, los que cruzan de una capa a otra. La capa de un
#    módulo de RPP, la de doc/control/capas.tsv; FOL y TheoryFramework, las suyas (debajo de todas); el fichero
#    generado, la pseudocapa CALIB, que sólo vale para la calibración.
CAPAS_TSV=doc/control/capas.tsv
CONTRATOS=doc/contratos
GEN_C="$TMP/contratos"
mkdir -p "$GEN_C"
if [ ! -f "$CAPAS_TSV" ]; then
  echo "  ❌ no existe $CAPAS_TSV: sin el manifiesto de las capas no hay contratos."
  exit 1
fi
# contratos USOS DIR: de cada uso «usado · su módulo · huella · módulo que lo usa», los que cruzan de capa, a DIR/CAPA.tsv
# (ordenados); y por la salida, «SINCAPA módulo» y «CALIB capa usado» (los usos desde la calibración, que no van a DIR)
contratos() {
  LC_ALL=C awk -F'\t' -v MAN="$CAPAS_TSV" -v OUT="$2" '
  function capaDe(m) {
    if (m in capa) return capa[m]
    if (m == "_calibracion") return "CALIB"
    if (m == "FOL" || index(m, "FOL.") == 1) return "FOL"
    if (m == "TheoryFramework" || index(m, "TheoryFramework.") == 1) return "TF"
    return ""
  }
  BEGIN {
    ORDEN = "FOL TF C0 C1 C2 C3 C4 C5 C6 C7.i C7.ii C7.iii C8 barril CALIB"
    n = split(ORDEN, O, " ")
    while ((getline l < MAN) > 0) { sub(/\r$/, "", l); split(l, f, "\t"); if (index(f[1], "ROBINSON_PlusPlus") == 1) capa[f[1]] = f[2] }
  }
  {
    cu = capaDe($2); cm = capaDe($4)
    if (cu == "") { sincapa[$2] = 1; next }
    if (cm == "") { sincapa[$4] = 1; next }
    if (cu == cm) next
    k = cu SUBSEP $1
    mod[k] = $2; hu[k] = $3
    if (!((k, cm) in visto)) { visto[k, cm] = 1; usan[k] = usan[k] " " cm }
  }
  END {
    for (x in sincapa) print "SINCAPA\t" x
    for (k in mod) {
      split(k, kk, SUBSEP)
      m = split(usan[k], us, " "); s = ""; cal = 0
      for (i = 1; i <= n; i++) for (j = 1; j <= m; j++) if (us[j] == O[i]) {
        if (O[i] == "CALIB") cal = 1; else s = s (s == "" ? "" : " ") O[i]
      }
      if (cal) print "CALIB\t" kk[1] "\t" kk[2]
      if (s != "") print kk[2] "\t" mod[k] "\t" hu[k] "\t" s > (OUT "/" kk[1] ".tsv")
    }
  }' "$1"
  for f in "$2"/*.tsv; do [ -f "$f" ] && LC_ALL=C sort -o "$f" "$f"; done
}
# la calibración de ESTA pieza, por el mismo camino (la de Lean no la ve: allí, lo de dentro del fichero de prueba ya lo
# quita el filtro de módulo, que sólo aligera, y el de capa quedaría tapado): unos usos inventados entre módulos reales
mkdir -p "$TMP/cal-contratos"
printf '%s\n' \
  $'prueba.a\tROBINSON_PlusPlus.Meta.NatArithPrf\t1\tROBINSON_PlusPlus.Meta.NatOrderPrf' \
  $'prueba.b\tROBINSON_PlusPlus.Meta.NatArithPrf\t2\tROBINSON_PlusPlus.Meta.Lob' \
  $'prueba.b\tROBINSON_PlusPlus.Meta.NatArithPrf\t2\tROBINSON_PlusPlus.Meta.DerivCondPrf' \
  $'prueba.b\tROBINSON_PlusPlus.Meta.NatArithPrf\t2\tROBINSON_PlusPlus.Meta.GodelTwoPrf' \
  $'prueba.c\tFOL.FOL\t3\tROBINSON_PlusPlus.Minimal.Axioms' \
  $'prueba.d\tROBINSON_PlusPlus.Meta.NoExiste\t4\tROBINSON_PlusPlus.Meta.Lob' \
  $'prueba.e\tROBINSON_PlusPlus.Meta.Lob\t5\t_calibracion' > "$TMP/cal-usos.tsv"
CAL_P=$( { contratos "$TMP/cal-usos.tsv" "$TMP/cal-contratos" | LC_ALL=C sort
           for f in "$TMP/cal-contratos"/*.tsv; do [ -f "$f" ] && sed "s|^|$(basename "$f" .tsv): |" "$f"; done; } )
ESP_P=$(printf '%s\n' $'CALIB\tC7.i\tprueba.e' $'SINCAPA\tROBINSON_PlusPlus.Meta.NoExiste' \
  $'C2: prueba.b\tROBINSON_PlusPlus.Meta.NatArithPrf\t2\tC3 C7.i' $'FOL: prueba.c\tFOL.FOL\t3\tC0')
if [ "$CAL_P" = "$ESP_P" ]; then
  echo "  ✓ calibración del cruce de capas: lo de una misma capa, fuera; las que usan, una vez y en orden; FOL; sin capa; CALIB"
else
  echo "  ❌ calibración del cruce de capas: con usos inventados no da lo esperado:"
  diff <(printf '%s\n' "$ESP_P") <(printf '%s\n' "$CAL_P") | sed 's/^/      /'
  FAIL=1
fi
tr -d '\r' < "$TMP/usos.crudo" | grep . > "$TMP/usos.tsv"
contratos "$TMP/usos.tsv" "$GEN_C" > "$TMP/contratos.salida"
SINCAPA=$(grep '^SINCAPA' "$TMP/contratos.salida" | cut -f2)
if [ -n "$SINCAPA" ]; then
  echo "  ❌ módulos sin capa en $CAPAS_TSV (los ve check-capas.bash): $(printf '%s ' $SINCAPA)"
  FAIL=1
fi
CAL_C=$(grep '^CALIB' "$TMP/contratos.salida" | LC_ALL=C sort)
ESP_C=$(LC_ALL=C sort <<'EOF'
CALIB	C1	ROBINSON_PlusPlus.Meta.Hilbert.Prf
CALIB	C1	ROBINSON_PlusPlus.Meta.Hilbert.Prfᵢ
CALIB	FOL	Formula
EOF
)
if [ "$CAL_C" = "$ESP_C" ]; then
  echo "  ✓ calibración de los contratos: Prf y Formula (por el tipo) y Prfᵢ (por el valor), de C1 y de FOL, y nada más"
else
  echo "  ❌ calibración de los contratos: la medida de los usos entre capas no dice lo esperado:"
  diff <(printf '%s\n' "$ESP_C") <(printf '%s\n' "$CAL_C") | sed 's/^/      /'
  FAIL=1
fi
for c in FOL C0 C1 C2 C3 C4 C5 C6; do
  if [ ! -s "$GEN_C/$c.tsv" ]; then
    echo "  ❌ la capa $c no tiene contrato: ninguna otra capa usa nada suyo (o la medida no lo ve)."
    FAIL=1
  fi
done
echo "  contratos: $(printf '%s\n' "$SALIDA" | awk -F'\t' '$1 == "USOS" { print $2 }') usos entre módulos; entre capas, por la capa de lo usado: $(for f in "$GEN_C"/*.tsv; do printf '%s %s · ' "$(basename "$f" .tsv)" "$(grep -c . "$f")"; done | sed 's/ · $//')"

if [ "$REHACER" = "1" ]; then
  {
    echo "# doc/indice.tsv — el ÍNDICE de las constantes DECLARADAS de RPP (sin las que genera Lean): nombre, clase, módulo y"
    echo "# enunciado, como lo imprime Lean con los nombres completos, en una línea. Lo genera y lo compara, en cada run de la CI,"
    echo "# check-indice.bash (L5-11, ADR-254); se rehace con «bash check-indice.bash --rehacer» en el commit que cambia una"
    echo "# declaración. Las de FOL y TheoryFramework, en ../FOL/doc/indice.tsv. Para buscar antes de construir:"
    echo "#   grep -i 'patrón' doc/indice.tsv ../FOL/doc/indice.tsv"
    echo "# nombre	clase	módulo	enunciado"
    cat "$GEN_I"
  } > "$INDICE"
  {
    echo "# doc/control/fol-sin-uso.tsv — las declaraciones de FOL y TheoryFramework que NINGUNA otra constante de RPP, FOL o"
    echo "# TheoryFramework nombra, en su tipo o en su valor (un constructor o un campo cuentan como su tipo); medido, no borrado"
    echo "# (FOL0912:B-5, ADR-254). La etiqueta: vigilada (fila de check-footprints: un titular), simp (simp puede usarla sin"
    echo "# rastro), instancia, meta (sintaxis o elaborador) o —. No cuenta los sondeos, el libro ni los consumidores archivados."
    echo "# La genera y la compara check-indice.bash; se rehace con «--rehacer»."
    echo "# módulo	nombre	clase	etiqueta"
    cat "$GEN_S"
  } > "$SINUSO"
  echo "  ✏️  $INDICE ($(grep -c . "$GEN_I") líneas) y $SINUSO ($(grep -c . "$GEN_S")), rehechas."
  mkdir -p "$CONTRATOS"
  for f in "$CONTRATOS"/*.tsv; do [ -f "$f" ] && [ ! -f "$GEN_C/$(basename "$f")" ] && rm -f "$f"; done
  for f in "$GEN_C"/*.tsv; do
    c=$(basename "$f" .tsv)
    case "$c" in
      FOL) d="FOL, la capa de debajo de todas: lo que RPP usa de la librería FOL (el contrato de ADR-139, paso 3.1)" ;;
      TF) d="TheoryFramework: lo que RPP usa de él" ;;
      *) d="$c ($(awk -F'\t' -v C="$c" '$1 == "capa" && $2 == C { print $3 }' "$CAPAS_TSV" | tr -d '\r'))" ;;
    esac
    {
      echo "# doc/contratos/$c.tsv — el CONTRATO de la capa $d:"
      echo "# lo que las OTRAS capas usan de ella (B1 paso 6, ADR-272). Cada constante declarada en un módulo de la capa que"
      echo "# nombra, en su tipo o en su valor, una constante declarada en un módulo de RPP de otra capa (las capas, en"
      echo "# doc/control/capas.tsv); la huella de su TIPO (Expr.hash; en un inductivo, con sus constructores: cambia si cambia"
      echo "# el enunciado, no la notación); y las capas que la usan. El enunciado, en doc/indice.tsv (o ../FOL/doc/indice.tsv)."
      echo "# Lo genera y lo compara check-indice.bash en cada run de la CI; se rehace con «bash check-indice.bash --rehacer»."
      echo "# nombre	módulo	huella del tipo	la usan"
      cat "$f"
    } > "$CONTRATOS/$c.tsv"
  done
  echo "  ✏️  $CONTRATOS/: $(ls "$GEN_C" | wc -l | tr -d ' ') contratos, rehechos."
fi

compara() {  # tabla generado nombre
  if [ ! -f "$1" ]; then
    echo "  ❌ no existe $1."
    FAIL=1
    return
  fi
  local decl="$TMP/declarado.$3"
  grep -v '^#' "$1" | tr -d '\r' | grep . | LC_ALL=C sort > "$decl"
  local nuevas idas
  nuevas=$(LC_ALL=C comm -13 "$decl" "$2")
  idas=$(LC_ALL=C comm -23 "$decl" "$2")
  if [ -z "$nuevas" ] && [ -z "$idas" ]; then
    echo "  ✓ $1: $(grep -c . "$decl") líneas, las que se generan"
  else
    echo "  ❌ $1 NO es lo que se genera ($(printf '%s\n' "$nuevas" | grep -c .) de más en lo generado, $(printf '%s\n' "$idas" | grep -c .) de menos): «bash check-indice.bash --rehacer»"
    printf '%s\n' "$nuevas" | grep . | head -15 | cut -c1-200 | sed 's/^/      + /'
    printf '%s\n' "$idas" | grep . | head -15 | cut -c1-200 | sed 's/^/      - /'
    FAIL=1
  fi
}
compara "$INDICE" "$GEN_I" indice
compara "$SINUSO" "$GEN_S" sinuso
for f in "$GEN_C"/*.tsv; do [ -f "$f" ] && compara "$CONTRATOS/$(basename "$f")" "$f" "contrato.$(basename "$f")"; done
for f in "$CONTRATOS"/*.tsv; do
  if [ -f "$f" ] && [ ! -f "$GEN_C/$(basename "$f")" ]; then
    echo "  ❌ $f sobra: esa capa ya no tiene contrato (nadie usa nada suyo): «bash check-indice.bash --rehacer»"
    FAIL=1
  fi
done

if [ "$FAIL" = "0" ]; then
  echo "✅ EL ÍNDICE, LO QUE NADIE USA DE FOL Y LOS CONTRATOS DE LAS CAPAS, AL DÍA."
else
  echo "❌ EL ÍNDICE, LO QUE NADIE USA DE FOL O LOS CONTRATOS DE LAS CAPAS NO CUADRAN (o la calibración falló)."
  exit 1
fi
